-- Prove2me | Theorems.Thm_GlobalTheory_zetaSeries_coeff_mul_le
-- name    : GlobalTheory.zetaSeries_coeff_mul_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:19.83761+00:00
-- url     : https://prove2.me/theorems/399cdfe1-935a-495f-b683-56b084e90408
-- title:
--   Global Theory: zeta Series coeff mul le
-- statement:
--   The Global Theory construction uses the zeta Series coeff mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZetaSeriesCoeffMulLe.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZetaSeriesCoeffMulLe.lean#L52-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZetaSeriesCoeffMulLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory
open MvPowerSeries
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ)) {M : ℕ} (ρ : Fin M → ℝ)

theorem GlobalTheory.zetaSeries_coeff_mul_le {c : C} {L : ℝ} (hc : ((L : ℝ) : WithTop ℝ) ≤ v c)
    {g : MvPowerSeries (Fin M) C} {s : ℝ} (hg : OrdGe v ρ g s) (α : Fin M →₀ ℕ) :
    (((L + s - ∑ m, ρ m * α m : ℝ)) : WithTop ℝ) ≤ v (c * coeff α g) := by sorry
