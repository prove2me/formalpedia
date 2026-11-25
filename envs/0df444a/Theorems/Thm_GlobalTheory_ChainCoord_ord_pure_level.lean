-- Prove2me | Theorems.Thm_GlobalTheory_ChainCoord_ord_pure_level
-- name    : GlobalTheory.ChainCoord.ord_pure_level
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:37:10.831795+00:00
-- url     : https://prove2.me/theorems/f4341e2c-c0a9-4b15-980e-021e5195f430
-- title:
--   Chain Coord: ord pure level
-- statement:
--   The Chain Coord construction uses the ord pure level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L218-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainLemmaMultivariatePowerSeriesCoordinateForm.lean#L218-L229

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
variable {C : Type} [Field C]

theorem GlobalTheory.ChainCoord.ord_pure_level {v : AddValuation C (WithTop ℝ)} {l : ℕ} (hl : 3 ≤ l)
    (hv : v (l : C) = 1) {d M : ℕ} {π : ℕ → Fin d → Fin M → C} {s : ℕ} {c : Fin d} {a σ : ℝ}
    (h : ∀ j, (a : WithTop ℝ) ≤ v (π s c j)) (j : Fin M) :
    ((a + 1 / ((l : ℝ) ^ 2 - 1) + ((l : ℝ) ^ 2) ^ s * σ -
      (1 / ((l : ℝ) ^ 2 - 1) + σ) * (((l ^ 2) ^ s : ℕ) : ℝ) : ℝ) : WithTop ℝ) ≤
        v (kap C l s * π s c j) := by sorry
