-- Prove2me | Theorems.Thm_GlobalTheory_zetaSeries_ordGe_mul
-- name    : GlobalTheory.zetaSeries_ordGe_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:35.542305+00:00
-- url     : https://prove2.me/theorems/75020dd3-3654-4d7e-b200-3bece31c6ac5
-- title:
--   Global Theory: zeta Series ord Ge mul
-- statement:
--   The Global Theory construction uses the zeta Series ord Ge mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZetaSeriesCoeffMulLe.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZetaSeriesCoeffMulLe.lean#L28-L42

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

theorem GlobalTheory.zetaSeries_ordGe_mul {f g : MvPowerSeries (Fin M) C} {r s : ℝ} (hf : OrdGe v ρ f r)
    (hg : OrdGe v ρ g s) : OrdGe v ρ (f * g) (r + s) := by sorry
