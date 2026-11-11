-- Prove2me | Theorems.Thm_KAQROM_lemma_5_10
-- name    : KAQROM.lemma_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:33:04.07242+00:00
-- url     : https://prove2.me/theorems/1de525c7-663c-4fd9-9859-6b401f6c4e16
-- title:
--   Lemma 5.10 — Barak–Mahmoody learner for classical two-party protocols
-- statement:
--   Consider a classical two-party random-oracle protocol with complete public transcript $M$ and views $U_P=(R_P,M,T_P)$, $P\in\{A,B\}$, in which Alice and Bob make at most $n_A$ and $n_B$ oracle queries, where $n_A,n_B\ge1$. Let $0<\varepsilon_1\le\varepsilon_2<1/10$. There is a deterministic classical-query algorithm $L^H_{\varepsilon_1,\varepsilon_2}(m)$ that on a complete public transcript $m$ outputs a partial oracle $h$, such that for all $0<\alpha_0,\beta_0<1$ with $\alpha_0\beta_0\ge\varepsilon_2$, writing $\mu^{AB}_{m,h}$ for the conditional distribution of $(U_A,U_B)$ given $M=m$, $L^H(m)=h$, with marginals $\mu^A_{m,h},\mu^B_{m,h}$:
--
--   1. the expected number of oracle queries of $L$ is at most $4n_An_B/\varepsilon_1$;
--   2. except with probability at most $9\alpha_0$ over the realized pair $(M,h)$,
--   $$
--   \Delta_{\mathrm{TV}}\bigl(\mu^{AB}_{M,h},\mu^A_{M,h}\times\mu^B_{M,h}\bigr)\le 9\beta_0 ;
--   $$
--   3. except with probability at most $9\alpha_0$ over $(M,h)$, every $x\notin\mathrm{Dom}(h)$ satisfies
--   $$
--   \Pr[x\in\mathrm{Dom}(T_A)\mid M,h]<\frac{\varepsilon_2}{n_B}+\beta_0,\qquad \Pr[x\in\mathrm{Dom}(T_B)\mid M,h]<\frac{\varepsilon_2}{n_A}+\beta_0 .
--   $$
--
--   This is the paper's restatement of Barak and Mahmoody's attacker, applied in Lemma 5.11 to the exact classical simulation of the quantum prefix.
--
--   **Formalization Note** Probabilities are over $H\leftarrow\mathcal H$ and the parties' randomness. The query bounds hold on every oracle and every choice of randomness of positive probability.
--
--   Differences from the source:
--   - encoding: a security parameter λ with inputs $1^\lambda$ → one fixed λ, $1^\lambda$ arguments dropped; reason: every statement of §5.2 is at one fixed λ with explicit constants
--   - generalization: $X=\{0,1\}^{n(\lambda)}$, $Y=\{0,1\}^{\ell(\lambda)}$ with $\ell(\lambda)\ge1$ → any finite type $X$ and any $\ell\in\mathbb N$, including $\ell=0$ (with $Y=\{0,1\}^\ell$ kept as bit strings, XOR as addition in $\mathbb Z_2^\ell$); reason: $n(\lambda)$, $\ell(\lambda)$ enter only through the sets $X$, $Y$ and no argument uses $\ell\ge1$; $X=\{0,1\}^n$, $\ell\ge1$ is an instance
--   - reading: "Let … $0<\alpha,\beta<1$, $\alpha\beta\ge\varepsilon_2$. There is … $L^H_{\varepsilon_1,\varepsilon_2}(m)$" → one $L$ for all $\alpha_0,\beta_0$ ($\exists L\,\forall\alpha_0\beta_0$); reason: the subscript shows that $L$ depends only on $\varepsilon_1,\varepsilon_2$; this is the stronger reading
--   - encoding: $\alpha$, $\beta$ → $\alpha_0$, $\beta_0$; reason: a rename: $\alpha$ is the agreement probability elsewhere
--   - encoding: a classical two-party random-oracle protocol with views $U_P=(R_P,M,T_P)$ → deterministic parties with private randomness on finite sets, alternating messages with Alice first and a fixed number of query steps (with "no query" allowed) per message; views stored as $(R_P,T_P)$; reason: dummy messages and idle steps pad any protocol; $M=m$ is fixed by the conditioning; random tapes and the simulation of §5.2.1 have finitely many values
--   - encoding: "except with probability at most $9\alpha$ over the realized pair $(M,h)$" → the probability, over $H$ and the randomness, of the complementary event at $(M,L^H(M))$ is at most $9\alpha_0$; reason: the realized pair is a function of the sample
--   - generalization: a deterministic classical-query algorithm that outputs a partial oracle $h$ → a decision tree on the transcript and the learned pairs whose output is the partial oracle of all its learned pairs; reason: a stronger existence claim (it implies the printed one); Barak–Mahmoody's Construction 3.3 learner outputs exactly the pairs it learned
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 5.10, p.34 ([BMG17, Construction 3.3, Definitions 4.1–4.2, Theorem 4.3, Items 2, 4, 5])

import Mathlib
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_QueryTree
import Definitions.Def_KAQROM_ClassicalProtocol

namespace KAQROM

/-- **Lemma 5.10 (Barak–Mahmoody).** Consider a classical two-party random-oracle protocol whose
parties make at most `n_A`, `n_B ≥ 1` oracle queries. Let `0 < ε₁ ≤ ε₂ < 1/10`. There is a
deterministic classical-query algorithm `L^H_{ε₁,ε₂}(m)` on complete public transcripts,
outputting a partial oracle `h`, such that for all `0 < α₀, β₀ < 1` with `α₀β₀ ≥ ε₂`:
(i) its expected number of oracle queries is at most `4 n_A n_B / ε₁`;
(ii) except with probability at most `9α₀` over the realized pair `(M, h)`,
`Δ_TV(μ^{AB}_{M,h}, μ^A_{M,h} × μ^B_{M,h}) ≤ 9β₀`;
(iii) except with probability at most `9α₀` over `(M, h)`, every `x ∉ Dom(h)` satisfies
`Pr[x ∈ Dom(T_A) | M, h] < ε₂/n_B + β₀` and `Pr[x ∈ Dom(T_B) | M, h] < ε₂/n_A + β₀`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 5.10, p.34 ([BMG17, Construction 3.3, Definitions 4.1–4.2, Theorem 4.3, Items 2,
4, 5]).

**Formalization Note.** The paper's `α, β` are renamed `α₀, β₀` (they clash with the agreement
probability). `L` is chosen before `α₀, β₀` (its subscript is `ε₁, ε₂` only). The query bounds
hold on every oracle and every choice of randomness of positive probability. Probabilities are
over `H ← ℋ` and the parties' randomness; "except with probability at most `9α₀`" is the
probability of the complementary event over the sample space. -/
theorem lemma_5_10 {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg : Type}
    (P : ClassicalProtocol X ℓ Msg) (nA nB : ℕ) (hnA : 1 ≤ nA) (hnB : 1 ≤ nB)
    (hq : ∀ (H : Oracle X ℓ) (rA : P.RndA) (rB : P.RndB), 0 < P.pA rA → 0 < P.pB rB →
      (P.exec H rA rB).2.1.length ≤ nA ∧ (P.exec H rA rB).2.2.length ≤ nB)
    (ε₁ ε₂ : ℝ) (hε₁ : 0 < ε₁) (hε₁₂ : ε₁ ≤ ε₂) (hε₂ : ε₂ < 1 / 10) :
    ∃ L : QueryTree (List Msg) X ℓ, ∀ α₀ β₀ : ℝ, 0 < α₀ → α₀ < 1 → 0 < β₀ → β₀ < 1 →
      ε₂ ≤ α₀ * β₀ →
      (∑ H : Oracle X ℓ, ∑ rA : P.RndA, ∑ rB : P.RndB,
          P.weight rA rB * ((L.learned H (P.exec H rA rB).1).length : ℝ)) ≤
        4 * nA * nB / ε₁ ∧
      (∑ H : Oracle X ℓ, ∑ rA : P.RndA, ∑ rB : P.RndB,
          if 9 * β₀ < tvDist (P.muAB L (P.exec H rA rB).1 (L.output H (P.exec H rA rB).1))
              (prodDist (P.muA L (P.exec H rA rB).1 (L.output H (P.exec H rA rB).1))
                (P.muB L (P.exec H rA rB).1 (L.output H (P.exec H rA rB).1)))
          then P.weight rA rB else 0) ≤ 9 * α₀ ∧
      (∑ H : Oracle X ℓ, ∑ rA : P.RndA, ∑ rB : P.RndB,
          if ∀ x, L.output H (P.exec H rA rB).1 x = none →
              P.condQueriedA L (P.exec H rA rB).1 (L.output H (P.exec H rA rB).1) x <
                  ε₂ / nB + β₀ ∧
                P.condQueriedB L (P.exec H rA rB).1 (L.output H (P.exec H rA rB).1) x <
                  ε₂ / nA + β₀
          then 0 else P.weight rA rB) ≤ 9 * α₀ := by sorry

end KAQROM
