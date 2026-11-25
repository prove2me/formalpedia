-- Prove2me | Theorems.Thm_GlobalTheory_T_det_bounded_convergent_powerSeries_matrix_eTwoPi
-- name    : GlobalTheory.T.det_bounded_convergent_powerSeries_matrix_eTwoPi
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:51.759748+00:00
-- url     : https://prove2.me/theorems/048892a2-c27e-4a5f-8a78-e9d6b43ce698
-- title:
--   T: det bounded convergent power Series matrix e Two Pi
-- statement:
--   The T construction uses the det bounded convergent power Series matrix e Two Pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DetBoundedConvergentPowerSeriesMatrixETwoPiStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DetBoundedConvergentPowerSeriesMatrixETwoPiStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DetBoundedConvergentPowerSeriesMatrixETwoPi
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DetBoundedConvergentPowerSeriesMatrixETwoPiStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.det_bounded_convergent_powerSeries_matrix_eTwoPi : ∀ (g : ℕ) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)) (w₀ : ℂ), IsUnit A.det → (∀ i j, Summable (fun m : ℕ => PowerSeries.coeff m (A i j) * eTwoPi w₀ ^ m)) → ∃ T' C : ℝ, 0 < C ∧ ∀ w : ℂ, T' < w.im → C⁻¹ ≤ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ∧ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ≤ C := by sorry
