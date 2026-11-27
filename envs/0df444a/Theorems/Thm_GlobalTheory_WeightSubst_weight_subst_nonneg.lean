-- Prove2me | Theorems.Thm_GlobalTheory_WeightSubst_weight_subst_nonneg
-- name    : GlobalTheory.WeightSubst.weight_subst_nonneg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:20.35256+00:00
-- url     : https://prove2.me/theorems/4a0cdb47-6951-4953-9337-5d286d075188
-- title:
--   Weight Subst: weight subst nonneg
-- statement:
--   The Weight Subst construction uses the weight subst nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WeightSubstNonneg.lean#L65-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WeightSubstNonneg.lean#L65-L79

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

theorem GlobalTheory.WeightSubst.weight_subst_nonneg :
  (∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (σ τ : Type) [Fintype σ] [DecidableEq σ] [Fintype τ] (ρ : σ → ℝ) (K : MvPowerSeries τ C) (t : τ → MvPowerSeries σ C),
    MvIsInt v K → (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ c, (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (t c)))) → (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (MvPowerSeries.subst t K)))) := by sorry
