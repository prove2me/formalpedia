-- Prove2me | Theorems.Thm_GlobalTheory_ChainCoord_coeff_pow_congr
-- name    : GlobalTheory.ChainCoord.coeff_pow_congr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:20.847991+00:00
-- url     : https://prove2.me/theorems/b891ef05-a5c2-4f87-90f4-c4092b95d966
-- title:
--   Chain Coord: coeff pow congr
-- statement:
--   The Chain Coord construction uses the coeff pow congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L61-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L61-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPowerSeries
open GlobalTheory GlobalTheory.ChainCoord
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ}

theorem GlobalTheory.ChainCoord.coeff_pow_congr {f g : MvPowerSeries (Fin M) C} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) {D m : ℕ} (hm : 2 ≤ m)
    (h : ∀ β : Fin M →₀ ℕ, Finsupp.degree β < D → coeff β f = coeff β g)
    (α : Fin M →₀ ℕ) (hα : Finsupp.degree α = D) : coeff α (f ^ m) = coeff α (g ^ m) := by sorry
