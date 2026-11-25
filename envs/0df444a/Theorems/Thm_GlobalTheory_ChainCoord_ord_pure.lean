-- Prove2me | Theorems.Thm_GlobalTheory_ChainCoord_ord_pure
-- name    : GlobalTheory.ChainCoord.ord_pure
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:37:38.12717+00:00
-- url     : https://prove2.me/theorems/94478acd-8ba2-4124-9ddd-cba68f893d9c
-- title:
--   Chain Coord: ord pure
-- statement:
--   The Chain Coord construction uses the ord pure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L48-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L48-L59

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

theorem GlobalTheory.ChainCoord.ord_pure {r w : ℝ} {N : ℕ} {a : Fin M → C}
    (h : ∀ j, ((w - r * N : ℝ) : WithTop ℝ) ≤ v (a j)) :
    OrdGe v (fun _ => r) (∑ j, MvPowerSeries.C (R := C) (a j) *
      (X j : MvPowerSeries (Fin M) C) ^ N) w := by sorry
