-- Prove2me | Theorems.Thm_GlobalTheory_zetaSeries_ordGe_pow
-- name    : GlobalTheory.zetaSeries_ordGe_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:40.978668+00:00
-- url     : https://prove2.me/theorems/19497720-a22b-4e59-a6e6-7d6111b1c60c
-- title:
--   Global Theory: zeta Series ord Ge pow
-- statement:
--   The Global Theory construction uses the zeta Series ord Ge pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZetaSeriesCoeffMulLe.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZetaSeriesCoeffMulLe.lean#L44-L50

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

theorem GlobalTheory.zetaSeries_ordGe_pow {f : MvPowerSeries (Fin M) C} {r : ℝ} (hf : OrdGe v ρ f r) (n : ℕ) :
    OrdGe v ρ (f ^ n) (n * r) := by sorry
