-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_strong_convergence_of_weak_convergence
-- name    : NemytskiiLebesgue.IsCaratheodory.strong_convergence_of_weak_convergence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:42.468094+00:00
-- url     : https://prove2.me/theorems/ccad4e44-b69a-434c-81ac-e2ecf7355625
-- title:
--   Is Caratheodory: strong convergence of weak convergence
-- statement:
--   The Is Caratheodory construction uses the strong convergence of weak convergence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/WeakConvergence.lean#L33-L56
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/WeakConvergence.lean#L33-L56

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali
public import Definitions.Def_LeanPool_NemytskiiLebesgue_WeakConvergence
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology

theorem NemytskiiLebesgue.IsCaratheodory.strong_convergence_of_weak_convergence
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : Ω → ℝ → ℝ} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {ι : X →L[ℝ] (Ω → ℝ)} (hιp : ∀ x : X, MemLp (ι x) p μ)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ, |f ω ξ| ≤ |a ω| + C * |ξ| ^ (p / q).toReal)
    {u : ℕ → X} (hup : UnifIntegrable (ι ∘ u) p μ)
    {v : X} (huv : u.NemytskiiWeaklyConvergesTo v) :
    (fun n : ℕ => fun ω : Ω => f ω (ι (u n) ω)).NemytskiiConvergesTo (fun ω : Ω => f ω (ι v ω)) q μ
      := by sorry
