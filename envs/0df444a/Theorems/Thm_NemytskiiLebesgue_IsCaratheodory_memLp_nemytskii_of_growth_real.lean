-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_memLp_nemytskii_of_growth_real
-- name    : NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_of_growth_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:09.336677+00:00
-- url     : https://prove2.me/theorems/00430bd3-dc79-42bb-a5ef-99c73251be66
-- title:
--   Is Caratheodory: mem Lp nemytskii of growth real
-- statement:
--   The Is Caratheodory construction uses the mem Lp nemytskii of growth real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Continuity.lean#L113-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Continuity.lean#L113-L124

module
public import Mathlib.MeasureTheory.Function.UnifTight
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal Topology

theorem NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_of_growth_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {u : Ω → ℝ^m} (hup : MemLp u p μ) :
    MemLp (fun ω : Ω => f ω (u ω)) q μ := by sorry
