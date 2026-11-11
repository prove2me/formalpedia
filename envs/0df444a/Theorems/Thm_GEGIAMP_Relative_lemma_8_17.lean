-- Prove2me | Theorems.Thm_GEGIAMP_Relative_lemma_8_17
-- name    : GEGIAMP.Relative.lemma_8_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:54:53.973397+00:00
-- url     : https://prove2.me/theorems/73befa9b-cdf4-4894-b1b7-2530756f0fd0
-- title:
--   Lemma 8.17 — sequential rounding and GOE norm/diagonal bounds
-- statement:
--   For symmetric $A$ and $v\in[-1,1]^N$, sequential rounding costs $O(N^2)$ and returns spins satisfying $H_N(\sigma)/N\ge H_N(v)/N-\frac1{2N}\sum_i|A_{ii}|$ (8.85). For GOE input, with probability at least $1-3e^{-u}$, $\|A\|\le2+2\sqrt{u/N}$ and $N^{-1}\sum_i|A_{ii}|\le(2+2\sqrt u)/\sqrt N$ (8.86).
--
--   Differences from the source:
--   - encoding: "sequential rounding costs O(N²) and returns spins" → `seqRound A v` has entries ±1 and satisfies (8.85); ∃ C such that for N ≥ 1 the machine routine `roundingProgram` halts on (A, v) with output `seqRound A v` and work ≤ C N²; reason: the cost is measured in the Definition 2.2 machine
--   - reading: u in (8.86) (range not stated) → every real u ≥ 0; reason: √u requires u ≥ 0; for u < 0 the bound 1 − 3e^{−u} is negative
--   - encoding: "with probability at least 1 − 3e^{−u}" → the outer GOE(N) measure of the failure set is ≤ 3e^{−u}, for N ≥ 1; reason: failure form; no measurability side condition
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Lemma 8.17, p. 59

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Algorithm

open MeasureTheory ProbabilityTheory OAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology

namespace GEGIAMP.Relative

/-- **Lemma 8.17** (sequential rounding; Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1, SHA-256 ea6508af…5658e, p. 59). For symmetric `A` and
`v ∈ [−1,1]^N`, sequential rounding costs `O(N²)` and returns spins with
`H_N(σ)/N ≥ H_N(v)/N − (1/(2N)) ∑_i |A_ii|` (8.85). For GOE input, with probability at least
`1 − 3e^{−u}`, `‖A‖ ≤ 2 + 2√(u/N)` and `N^{−1} ∑_i |A_ii| ≤ (2 + 2√u)/√N` (8.86). -/
theorem lemma_8_17 :
    (∀ (N : ℕ) (A : Fin N → Fin N → ℝ), IsSymm A → ∀ v : Fin N → ℝ, (∀ i, |v i| ≤ 1) →
      IsSpin (seqRound A v) ∧
      H A (seqRound A v) / N ≥ H A v / N - 1 / (2 * N) * ∑ i, |A i i|) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (O : Oracles) (N : ℕ), 1 ≤ N → ∀ (A : Fin N → Fin N → ℝ), IsSymm A →
      ∀ v : Fin N → ℝ, (∀ i, |v i| ≤ 1) →
        ∃ s : State, finalState O roundingProgram (roundInit N A v) = some s ∧
          outVec N s = seqRound A v ∧ (s.work : ℝ) ≤ C * N ^ 2) ∧
    (∀ (N : ℕ), 1 ≤ N → ∀ u : ℝ, 0 ≤ u →
      RandMatDisc.goe N {A | ¬ (opNorm A ≤ 2 + 2 * Real.sqrt (u / N) ∧
          (∑ i, |A i i|) / N ≤ (2 + 2 * Real.sqrt u) / Real.sqrt N)} ≤
        ENNReal.ofReal (3 * Real.exp (-u))) := by sorry

end GEGIAMP.Relative
