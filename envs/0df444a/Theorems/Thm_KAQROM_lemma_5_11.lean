-- Prove2me | Theorems.Thm_KAQROM_lemma_5_11
-- name    : KAQROM.lemma_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:32.869328+00:00
-- url     : https://prove2.me/theorems/dda7f444-2e3d-4d82-ad6a-8aae04511626
-- title:
--   Lemma 5.11 — the Barak–Mahmoody prefix attacker $\mathsf{Learn}^{\mathsf{BM}}_\eta$ with $Q_{\mathsf{learn}}=\lceil 4\cdot10^5\bar q_A\bar q_B/\eta^3\rceil$ queries
-- statement:
--   Let $\Pi^{\mathrm{mr}}$ satisfy Definition 3.10, let $0<\eta<1/100$, and set
--   $$
--   \bar q_A=\max\{1,q_{A,\mathrm{pre}}\},\qquad \bar q_B=\max\{1,q_{B,\mathrm{pre}}\},\qquad Q_{\mathsf{learn}}=\Bigl\lceil\frac{4\cdot10^5\,\bar q_A\bar q_B}{\eta^3}\Bigr\rceil .
--   $$
--   There is a deterministic algorithm $\mathsf{Learn}^{\mathsf{BM},H}_\eta$ with classical oracle access that, on a complete public prefix transcript $m$, outputs a partial oracle $h$ or aborts, such that, with $(m,h)$ reachable when $\Pr[M=m,\ \mathsf{Learn}^{\mathsf{BM},H}_\eta(m)=h]>0$:
--
--   1. it makes at most $Q_{\mathsf{learn}}$ oracle queries and aborts with probability at most $\eta$;
--   2. for every reachable $(m,h)$, $\tfrac12\|\omega^{AB}_{m,h}-\omega^A_{m,h}\otimes\omega^B_{m,h}\|_1\le\eta$;
--   3. for every reachable $(m,h)$ and every $x\notin\mathrm{Dom}(h)$, $\Pr[x\in\mathrm{Dom}(T_A)\mid\mathsf F_{m,h}]\le\eta$;
--   4. for every reachable $(m,h)$ and every oracle $H$, $\mathsf{Learn}^{\mathsf{BM},H}_\eta(m)=h\iff h\preceq H$.
--
--   This is the learning phase of the attack; its query bound is the classical-query term of Theorem 5.14.
--
--   **Formalization Note** The query bound holds on every oracle and every input transcript. Properties 1 (abort), 2, 3 and 4 are the predicate `IsBMPrefixLearner`.
--
--   Differences from the source:
--   - encoding: a security parameter λ with inputs $1^\lambda$ → one fixed λ, $1^\lambda$ arguments dropped; reason: every statement of §5.2 is at one fixed λ with explicit constants
--   - generalization: $X=\{0,1\}^{n(\lambda)}$, $Y=\{0,1\}^{\ell(\lambda)}$ with $\ell(\lambda)\ge1$ → any finite type $X$ and any $\ell\in\mathbb N$, including $\ell=0$ (with $Y=\{0,1\}^\ell$ kept as bit strings, XOR as addition in $\mathbb Z_2^\ell$); reason: $n(\lambda)$, $\ell(\lambda)$ enter only through the sets $X$, $Y$ and no argument uses $\ell\ge1$; $X=\{0,1\}^n$, $\ell\ge1$ is an instance
--   - encoding: quantum oracle algorithms making at most $q$ queries, alternating oracle-independent operations with $U_H$ → exactly $q$ query rounds interleaved with arbitrary channels (Kraus families), then a measurement; reason: a query on the response state $|+\rangle^{\otimes\ell}$ is idle, so any algorithm pads to exactly $q$; parties are computationally unbounded (Stinespring)
--   - encoding: classical oracle access in the prefix (Definition 3.1); stages $A_i$, $B_i$ with residual registers → each stage is $D$ query steps and one message step, each a quantum instrument selected by the party's classical record (messages so far, own query–answer list, step index); a step with outcome none makes no query; one fixed register per party; reason: this is Definition 3.1's classical access (answers returned classically and recorded); idle steps and a large enough register pad any finite stage
--   - encoding: keys in $K_\lambda\cup\{\bot\}$ → `Option K` with ⊥ = `none`; reason: same values
--   - encoding: $q_{A,\mathrm{pre}} := \max|T_A|$, $q_{B,\mathrm{pre}} := \max|T_B|$ → the maximum over every oracle and every prefix branch of positive probability; reason: the paper's worst case over executions
--   - encoding: $\omega^{AB}_{m,h}$ defined through the exact classical simulation and the channels $\Phi_A\otimes\Phi_B$ → $\omega^{AB}_{m,h}$ defined as the $T_AS_AT_BS_B$-marginal of $\Omega_{m,h}$, with $\omega^A$, $\omega^B$ its marginals; reason: the paper states the two are equal ("Since the simulation is exact", p.33)
--   - encoding: $\tfrac12\|\cdot\|_1$ on states classical on $(H,T_A,T_B)$ → half the sum of the trace norms of the blocks; reason: exact for block-diagonal operators
--   - encoding: a deterministic algorithm with classical oracle access that outputs a partial oracle or aborts → a decision tree on the transcript and the learned pairs, with an abort decision after its queries; reason: an unbounded deterministic classical-query algorithm is such a tree
--   - generalization: "outputs a partial oracle $h$" → the non-abort output is the partial oracle of all the pairs the learner queried; reason: a stronger existence claim (it implies the printed one); the learner of the proof, Barak–Mahmoody's Construction 3.3 truncated, outputs exactly its learned pairs ("every pair in $h$ was obtained from an oracle query", p.36)
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 5.11, p.35

import Mathlib
import Definitions.Def_KAQROM_Protocol
import Definitions.Def_KAQROM_QueryTree
import Definitions.Def_KAQROM_Protocol_Omega
import Definitions.Def_KAQROM_IsBMPrefixLearner

namespace KAQROM

/-- **Lemma 5.11 (Barak–Mahmoody prefix attacker).** Let `0 < η < 1/100`,
`q̄_A = max{1, q_{A,pre}}`, `q̄_B = max{1, q_{B,pre}}`, `Q_learn = ⌈4·10⁵ q̄_A q̄_B / η³⌉`. There is
a deterministic algorithm `Learn^{BM,H}_η` with classical oracle access that, on a complete
public prefix transcript `m`, outputs a partial oracle `h` or aborts, makes at most `Q_learn`
oracle queries (on every oracle and every input), and has the properties of
`IsBMPrefixLearner`: it aborts with probability at most `η`; for every reachable `(m, h)`,
`½‖ω^{AB}_{m,h} − ω^A_{m,h} ⊗ ω^B_{m,h}‖₁ ≤ η` and `Pr[x ∈ Dom(T_A) | F_{m,h}] ≤ η` for every
`x ∉ Dom(h)`; and for every reachable `(m, h)` and every oracle `H`,
`Learn^{BM,H}_η(m) = h ⟺ h ⪯ H`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 5.11, p.35. -/
theorem lemma_5_11 {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
    [DecidableEq Msg] [Fintype K] (P : Protocol X ℓ Msg K) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1 / 100) :
    ∃ L : PrefixLearner (Fin P.n → Msg) X ℓ,
      (∀ (H : Oracle X ℓ) (m : Fin P.n → Msg), (L.learned H m).length ≤
        ⌈4 * 10 ^ 5 * ((max 1 P.qApre : ℕ) : ℝ) * ((max 1 P.qBpre : ℕ) : ℝ) / η ^ 3⌉₊) ∧
      IsBMPrefixLearner P η L := by sorry

end KAQROM
