-- Prove2me | Theorems.Thm_NoPerfectRandComp_Supplement_theorem_4_1
-- name    : NoPerfectRandComp.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:22:48.46414+00:00
-- url     : https://prove2.me/theorems/4bd365d7-c48a-4b92-94c0-61a51c78386d
-- title:
--   Theorem 4.1 — total noisy-query separation: $\mathrm{R}(W_q)>25\ell_qu_q^2q^3$, $\mathrm{noisyR}(W_q)=O(\ell_q\log(\ell_q+2)u_q^2q^2)$
-- statement:
--   **Total noisy-query separation.** Let $W_q$ ($q\ge4$) be the total Boolean functions of Definition 4.7, built from any private cell encoding, write $\ell_q = \lceil\log_2 q\rceil$ and $u_q = 10000q^4 + 2^{10000q^4+1}$, and let $N_q = c_q u_q^3 + 36a_q2^{c_q}$ be the number of input bits. Then every $W_q$ is nonconstant, and
--   $$
--   \mathrm{R}(W_q) > 25\,\ell_q u_q^2q^3,\qquad \mathrm{noisyR}(W_q) = O\bigl(\ell_q\log(\ell_q+2)\,u_q^2q^2\bigr).
--   $$
--   Consequently
--   $$
--   \frac{\mathrm{R}(W_q)}{\mathrm{noisyR}(W_q)} = \Omega\Bigl(\frac{q}{\log\log(q+2)}\Bigr),
--   $$
--   $\log N_q = \Theta(q^4)$, and for all sufficiently large $q$
--   $$
--   \frac{\mathrm{R}(W_q)}{\mathrm{noisyR}(W_q)} = \Omega\Bigl(\frac{(\log N_q)^{1/4}}{\log\log\log N_q}\Bigr).
--   $$
--
--   Here $\mathrm{noisyR}$ is the worst-input expected cost of an algorithm making noisy queries (correlation $\gamma$, cost $\gamma^2$) with error at most $1/3$. Weak noisy queries are therefore asymptotically cheaper than ordinary randomized queries on a total function.
--
--   **Formalization Note** $\log$ is $\log_2$ and $\ell_q$ is `Nat.clog 2 q`. The constants are uniform in $q\ge4$ and in the encoding; the last bound has a threshold $q_0$. Ratios are multiplied out in $[0,\infty]$.
--
--   Differences from the source:
--
--   - generalization: W_q with the paper's fixed (lexicographically first) encoding → W_q for every admissible encoding (private linear map and surjective decoder); reason: the base mission's convention (Lemma 4.9); the proof uses only privacy (Lemma 4.5) and surjectivity, and the paper's encoding is admissible
--   - reading: there is a family W_q → the paper's own family W_q of Definition 4.7; reason: §4 constructs W_q as the witness; naming it is the stronger reading and implies the existential
--   - encoding: Θ, O, Ω in q → explicit constants 0 < c, C uniform over q ≥ 4 and encodings; threshold q₀ for the clause stated for sufficiently large q; ratios multiplied out in ℝ≥0∞; reason: standard reading; the multiplied-out ratio is equivalent because noisyR(W_q) is finite by the O clause
--   - encoding: N_q, the number of input bits → Fintype.card of the index type of the function; reason: the cardinality is the number of input bits
--   - encoding: noisy algorithm (randomised, adaptive, correlations γ ∈ [0,1]) → NoisyAlg: an adaptive strategy on histories of answers and fair internal coins, possibly infinite; reason: covers distributions over noisy trees, including a.s.-halting ones; fair coins generate the internal randomness
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Theorem 4.1, p.11 (W_q: Definition 4.7, p.16)

import Mathlib
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_IsNonconst
import Definitions.Def_NoPerfectRandComp_W
import Definitions.Def_NoPerfectRandComp_Supplement_noisyReps
open scoped ENNReal

namespace NoPerfectRandComp

namespace Supplement

/-- Theorem 4.1 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.11 (total noisy-query separation): the total Boolean
functions `W_q` (`q ≥ 4`) are nonconstant and, with `ℓ_q = ⌈log₂ q⌉`,
`u_q = 10000 q⁴ + 2^{10000 q⁴ + 1}`,
`R(W_q) > 25 ℓ_q u_q² q³`, `noisyR(W_q) = O(ℓ_q log(ℓ_q + 2) u_q² q²)`; consequently
`R(W_q)/noisyR(W_q) = Ω(q / log log(q + 2))`. The number of input bits `N_q` satisfies
`log N_q = Θ(q⁴)`, giving a separation `Ω((log N_q)^{1/4} / log log log N_q)` for sufficiently
large `q`.

**Formalization Note** `W_q` is the published `W q enc` (Definition 4.7), and the theorem holds for
every private cell encoding `enc` (the paper fixes one). `ℓ_q` is `Nat.clog 2 q`, `log` is
`Real.logb 2`, `N_q = |WIdx q| = c_q u_q³ + 36 a_q 2^{c_q}`. The `O`, `Ω` and `Θ` clauses have
explicit constants `c, C > 0`, uniform in `q ≥ 4` and `enc`; the last clause, stated "for
sufficiently large `q`", has a threshold `q₀`. Ratios are multiplied out in `ℝ≥0∞`. -/
theorem theorem_4_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) (enc : Encoding (aq q) (WCell q)), 4 ≤ q →
      IsNonconst (W q enc) ∧
      25 * Nat.clog 2 q * uq q ^ 2 * q ^ 3 < Rt (W q enc) ∧
      noisyR (PartialFn.total (W q enc)) ≤
        ENNReal.ofReal (C * (Nat.clog 2 q : ℝ) * Real.logb 2 ((Nat.clog 2 q : ℝ) + 2) *
          (uq q : ℝ) ^ 2 * (q : ℝ) ^ 2) ∧
      ENNReal.ofReal (c * q / Real.logb 2 (Real.logb 2 ((q : ℝ) + 2))) *
          noisyR (PartialFn.total (W q enc)) ≤ (Rt (W q enc) : ℝ≥0∞) ∧
      c * (q : ℝ) ^ 4 ≤ Real.logb 2 (Fintype.card (WIdx q)) ∧
      Real.logb 2 (Fintype.card (WIdx q)) ≤ C * (q : ℝ) ^ 4 ∧
      (q₀ ≤ q →
        ENNReal.ofReal (c * Real.logb 2 (Fintype.card (WIdx q)) ^ ((1 : ℝ) / 4) /
            Real.logb 2 (Real.logb 2 (Real.logb 2 (Fintype.card (WIdx q))))) *
          noisyR (PartialFn.total (W q enc)) ≤ (Rt (W q enc) : ℝ≥0∞)) := by sorry

end Supplement

end NoPerfectRandComp
