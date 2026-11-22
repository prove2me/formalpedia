-- Prove2me | Theorems.Thm_NemytskiiLebesgue_frechet_remainder_le_of_all_in_set_icc_zero_one_norm_le
-- name    : NemytskiiLebesgue.frechet_remainder_le_of_all_in_set_icc_zero_one_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:26.561099+00:00
-- url     : https://prove2.me/theorems/f3a4b3d2-9eae-4f61-8d8a-d68a170eb193
-- title:
--   Nemytskii Lebesgue: frechet remainder le of all in set icc zero one norm le
-- statement:
--   The Nemytskii Lebesgue construction uses the frechet remainder le of all in set icc zero one norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L27-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L27-L49

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology

theorem NemytskiiLebesgue.frechet_remainder_le_of_all_in_set_icc_zero_one_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {g' : E → E →L[ℝ] F} (hgg' : ∀ ξ : E, HasFDerivAt g (g' ξ) ξ)
    {x e : E} {M : ℝ} (hxeM : ∀ t : ℝ, t ∈ Set.Icc 0 1 → ‖g' (x + t • e) - g' x‖ ≤ M) :
    ‖g (x + e) - g x - g' x e‖ ≤ M * ‖e‖ := by sorry
