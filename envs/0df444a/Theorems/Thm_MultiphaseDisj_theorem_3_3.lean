-- Prove2me | Theorems.Thm_MultiphaseDisj_theorem_3_3
-- name    : MultiphaseDisj.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:31:41.065484+00:00
-- url     : https://prove2.me/theorems/21d6c69c-c18e-437d-bd10-5481ad9dc1b0
-- title:
--   Theorem 3.3 — simulation theorem: a data structure gives a 2.5-round protocol
-- statement:
--   Assume the standing hypotheses of §3: $0<c_1\le c_2$, $n\ge n_0(c_1,c_2)$, $c_1\ln n\le w\le c_2\ln n$, integers $t_u\ge1$ and reals $t_q\ge1$ with $t_uw\le n^{1/95}$ and $t_q\le\log_2^2 n$. Let $\mathcal D$ be a deterministic structure (the tape fixed) with zero error, worst-case update time $t_u$ and $\mathbb E_{\mathcal D,Q}[T(Q)]\le t_q$ under the hard distribution. Let $U$ consist of the two lists of the cells of $C_i$ and of $C_{<i}$ with their final contents, let $p=\varepsilon/(32t_uw)$ with $\varepsilon=1/40$, and let $R_{\mathrm{Bob}}$ consist of independent bits $R_a$ with $\Pr[R_a=1]=p$, one per cell.
--
--   For every $i\in I$ there is a 2.5-round protocol $G_i$ for the game of Protocol 1 in which Merlin sends $U$ and Bob's message has the form $\Phi=(X^{(\neq i)},\Psi)$, such that, with $B_Q$ the indicator that Bob outputs "disjoint" and $\rho_1=\Pr_{\mathcal D,R_{\mathrm{Bob}},Q}[B_Q=1]$:
--
--   1. (a) (zero error) if Bob does not output FAIL, his output is the correct answer; in particular $B_Q=1$ implies $S_Q\cap X=\emptyset$;
--   2. (b) $|U|\le5t_uws_i$ and $|\Psi|\le\varepsilon s_i/4$;
--   3. (c) $|A_q|\le17t_qw$ for every $q\in[m]$;
--   4. (d) $$\rho_1\ge\frac18\,p^{8\tau_i}-e^{-n^{1/4}/3};$$
--   5. (e) $\Psi$ is a function of $(U,R_{\mathrm{Bob}})$, each $A_q$ is a function of $(\vec S,\Phi)$, and $B_Q$ is a function of $(\Psi,A_Q,U)$.
--
--   This is Step 1 of the proof: a data structure whose queries read few cells of epoch $i$ yields a protocol that certifies "disjoint" with non-negligible probability while revealing little.
--
--   Differences from the source:
--   - reading: standing assumptions of §3 (w = Θ(log n), tu w ≤ n^{1/95}, tq ≤ log² n, tu, tq ≥ 1, n sufficiently large) → hypotheses: ∀ 0 < c₁ ≤ c₂, ∃ n₀, ∀ n ≥ n₀, ∀ w with c₁ ln n ≤ w ≤ c₂ ln n, 1 ≤ tu, 1 ≤ tq, tu w ≤ n^{1/95}, tq ≤ (log₂ n)²; reason: §3.1 Setup, p.16, and §2.1 'state asymptotic bounds for sufficiently large instances'
--   - reading: 'the data structure' of the Setup (tape fixed by averaging, p.16) → any deterministic structure (tape type Unit) with zero error, worst-case update time tu and E_{D,Q}[T(Q)] ≤ tq; reason: these are the properties the Setup gives
--   - encoding: message lengths |·| ≤ λ bits → at most 2^λ values on the support of the joint law; reason: p.17: 'a message of length λ takes at most 2^λ values'
--   - encoding: Merlin's two lists of cells with final contents → two finite sets of (address, final content) pairs; reason: the order of a list carries no information
--   - reading: (e) B_Q is a function of (Ψ, A_Q, U) → Bob's whole output (disjoint, intersecting or FAIL) is a function of (Ψ, A_Q, U); reason: this is how Protocol 2 computes it; it implies (e)
--   - reading: (a) 'his output is the correct answer' and (b), (c) → stated on the support of the joint law of ((S⃗, X), Q, R_Bob); reason: the game is played on inputs of the hard distribution (the protocol is built from the epochs of D); off the support X may have elements outside the blocks, which the hard insertion sequence never inserts
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Theorem 3.3, p.17 (Protocol 2, p.18)

import Mathlib
import Definitions.Def_MultiphaseDisj_Epochs
import Definitions.Def_MultiphaseDisj_Protocol

set_option autoImplicit false

namespace MultiphaseDisj

/-- **Theorem 3.3 (Simulation theorem)** (Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held
version sha256 ba26649b…, Theorem 3.3, p.17; Protocol 2, p.18). Let the
data structure be deterministic (the tape fixed, p.16), with zero error, worst-case update time
`tu`, and `E_{D,Q}[T(Q)] ≤ tq`. Let `U` consist of the two lists of the cells of `Cᵢ` and of
`C_{<i}` with their final contents, let `p := ε/(32 tu w)`, and let Bob's randomness `R_Bob`
consist of an independent bit `R_a` with `Pr[R_a = 1] = p` for every cell `a`, independent of
`(S⃗, X)` and `Q`. For every `i ∈ I` there is a 2.5-round protocol `Gᵢ` for the game of
Protocol 1, in which Merlin sends `U` and Bob's message has the form `Φ = (X^{(≠i)}, Ψ)`, with:

* (a) (Zero error) if Bob does not output FAIL, his output is the correct answer; in particular
  `B_Q = 1` implies `S_Q ∩ X = ∅`;
* (b) `|U| ≤ 5 tu w sᵢ` and `|Ψ| ≤ ε sᵢ / 4`;
* (c) `|A_q| ≤ 17 tq w` for every `q ∈ [m]`;
* (d) `ρ₁ ≥ (1/8) p^{8 τᵢ} − e^{−n^{1/4}/3}`, where `ρ₁ = Pr_{D,R_Bob,Q}[B_Q = 1]`;
* (e) `Ψ` is a function of `(U, R_Bob)`, each `A_q` of `(S⃗, Φ)`, and `B_Q` of `(Ψ, A_Q, U)`.

**Formalization Note** The standing assumptions of §3 (p.16) are hypotheses: `c₁ log n ≤ w ≤
c₂ log n` for arbitrary `0 < c₁ ≤ c₂`, `n ≥ n₀(c₁, c₂)`, `tu w ≤ n^{1/95}`, `tq ≤ log₂² n`,
`tu, tq ≥ 1`. A deterministic structure is a `DisjStructure` with tape type `Unit`. Message
lengths are numbers of values on the support (`|·| ≤ λ` as at most `2^λ` values); (e) is the
argument structure of `Protocol`, and the whole output of Bob is a function of `(Ψ, A_Q, U)`, as in
Protocol 2. `ε = 1/40`. -/
theorem theorem_3_3 :
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ c₂ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ w : ℕ, c₁ * Real.log n ≤ w → (w : ℝ) ≤ c₂ * Real.log n →
      ∀ (tu : ℕ) (tq : ℝ), 1 ≤ tu → 1 ≤ tq →
      ((tu * w : ℕ) : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 95) → tq ≤ (Real.logb 2 n) ^ 2 →
      ∀ D : DisjStructure n n w Unit, D.ZeroError → D.UpdateCostLE tu →
      expect (dqLaw n (tu * w))
          (fun ω => (Epochs.queryCost D (tu * w) ω.1.1 ω.1.2 ω.2 : ℝ)) ≤ tq →
      ∀ i ∈ epochSet n (tu * w),
      ∃ (PT AT : Type) (G : Protocol n (Word w → Bool)
          (Finset (Word w × Word w) × Finset (Word w × Word w)) PT AT),
        G.U = Epochs.merlinMsg D (tu * w) i ∧
        -- (a), first sentence
        (∀ ω, jointLaw n (tu * w) (bernLaw w (pSample tu w)) ω ≠ 0 →
          ∀ b : Bool, G.out (block n (tu * w) i) ω = some b →
            b = decide (Disjoint (ω.1.1 ω.2.1) ω.1.2)) ∧
        -- (a) "in particular", (b), (c)
        G.IsSimProtocol (bernLaw w (pSample tu w)) w tu tq i ∧
        -- (d)
        (1 / 8 : ℝ) * pSample tu w ^ (8 * Epochs.tau D (tu * w) i) -
            Real.exp (-((n : ℝ) ^ ((1 : ℝ) / 4)) / 3) ≤
          G.rho1 (tu * w) (bernLaw w (pSample tu w)) (block n (tu * w) i) := by sorry

end MultiphaseDisj
