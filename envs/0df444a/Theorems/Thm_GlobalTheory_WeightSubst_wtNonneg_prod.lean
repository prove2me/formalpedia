-- Prove2me | Theorems.Thm_GlobalTheory_WeightSubst_wtNonneg_prod
-- name    : GlobalTheory.WeightSubst.wtNonneg_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:34:29.603503+00:00
-- url     : https://prove2.me/theorems/163e0dc7-a1a8-4be9-b932-0bc3e8ffd2cb
-- title:
--   Weight Subst: wt Nonneg prod
-- statement:
--   The Weight Subst construction uses the wt Nonneg prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WeightSubstNonneg.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WeightSubstNonneg.lean#L46-L54

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

theorem GlobalTheory.WeightSubst.wtNonneg_prod {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries σ C)
    (h : ∀ i ∈ s, WtNonneg v ρ (f i)) : WtNonneg v ρ (∏ i ∈ s, f i) := by sorry
