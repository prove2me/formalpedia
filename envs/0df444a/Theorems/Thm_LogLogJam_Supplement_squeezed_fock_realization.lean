-- Prove2me | Theorems.Thm_LogLogJam_Supplement_squeezed_fock_realization
-- name    : LogLogJam.Supplement.squeezed_fock_realization
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T19:14:29.216379+00:00
-- url     : https://prove2.me/theorems/8e488716-35ca-5ac9-bd41-a236dca6f656
-- title:
--   Realization of a squeezed vacuum by its even Fock amplitudes
-- statement:
--   For every nonnegative squeezing r and angle θ, a density with the corresponding centered Gaussian covariance exists. In the number basis its entries are the rank-one outer product of the normalized even squeezed amplitudes. The odd amplitudes vanish.
-- source:
--   https://arxiv.org/abs/2607.12983; Lemmas 4.1, 4.6 and §8.3, Eq. (144).

import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
import Definitions.Def_BosonicLearn_traceDist
open LogLogJam Matrix
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal

namespace LogLogJam.Supplement
theorem squeezed_fock_realization (r θ : ℝ) (hr : 0 ≤ r) :
    let z := (Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ) * Complex.I)
    let w := fun n : ℕ => if Even n then
      ((Real.sqrt (Nat.centralBinom (n/2) : ℝ) / ((2:ℝ)^(n/2) * Real.sqrt (Real.cosh r)) : ℝ) : ℂ) * z^(n/2) else 0
    ∃ ρ : State (Occupation (Fin 1)), squeezedAt ρ r θ ∧
      ∀ u v, ρ.coefficients u v = w (u 0) * star (w (v 0)) := by sorry
end LogLogJam.Supplement
