-- Prove2me | Theorems.Thm_GlobalTheory_zetaSeries_ordGe_mono
-- name    : GlobalTheory.zetaSeries_ordGe_mono
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:50:18.326662+00:00
-- url     : https://prove2.me/theorems/e7d3cf38-64db-4000-8c72-8bd383297c89
-- title:
--   Global Theory: zeta Series ord Ge mono
-- statement:
--   The Global Theory construction uses the zeta Series ord Ge mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZetaSeriesCoeffMulLe.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZetaSeriesCoeffMulLe.lean#L17-L19

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

theorem GlobalTheory.zetaSeries_ordGe_mono {g : MvPowerSeries (Fin M) C} {r s : ℝ} (h : OrdGe v ρ g r)
    (hsr : s ≤ r) : OrdGe v ρ g s := by sorry
