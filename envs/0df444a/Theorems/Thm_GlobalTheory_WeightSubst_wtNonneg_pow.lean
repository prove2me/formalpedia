-- Prove2me | Theorems.Thm_GlobalTheory_WeightSubst_wtNonneg_pow
-- name    : GlobalTheory.WeightSubst.wtNonneg_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:34:20.203212+00:00
-- url     : https://prove2.me/theorems/816a0c8f-d20a-4bb7-9849-8267276ccda0
-- title:
--   Weight Subst: wt Nonneg pow
-- statement:
--   The Weight Subst construction uses the wt Nonneg pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WeightSubstNonneg.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WeightSubstNonneg.lean#L57-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightSubstNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.WeightSubst
open MvPowerSeries
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type} [Fintype σ]
  [DecidableEq σ] (ρ : σ → ℝ)
omit [Fintype σ]

theorem GlobalTheory.WeightSubst.wtNonneg_pow {f : MvPowerSeries σ C} (hf : WtNonneg v ρ f) (n : ℕ) :
    WtNonneg v ρ (f ^ n) := by sorry
