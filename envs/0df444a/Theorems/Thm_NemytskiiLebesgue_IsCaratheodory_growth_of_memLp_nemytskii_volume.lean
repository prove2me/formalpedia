-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_growth_of_memLp_nemytskii_volume
-- name    : NemytskiiLebesgue.IsCaratheodory.growth_of_memLp_nemytskii_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:28.06217+00:00
-- url     : https://prove2.me/theorems/01697331-e410-4341-bbdf-5dd4631f3a14
-- title:
--   Is Caratheodory: growth of mem Lp nemytskii volume
-- statement:
--   The Is Caratheodory construction uses the growth of mem Lp nemytskii volume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/ConverseImplication.lean#L1034-L1049
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/ConverseImplication.lean#L1034-L1049

module
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_ConverseImplication
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter TopologicalSpace
open scoped NNReal ENNReal Topology

theorem NemytskiiLebesgue.IsCaratheodory.growth_of_memLp_nemytskii_volume
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k} (hf : IsCaratheodory f volume)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    (hpqf : ∀ u : ℝ → ℝ^m, MemLp u p volume → MemLp (fun x : ℝ => f x (u x)) q volume) :
    ∃ a : ℝ → ℝ, MemLp a q volume ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ x : ℝ ∂volume, ∀ ξ : ℝ^m, ‖f x ξ‖ ≤ |a x| + C * ‖ξ‖ ^ (p / q).toReal := by sorry
