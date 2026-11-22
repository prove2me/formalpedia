-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_nemytskii_seqContinuous_of_memLp_of_growth_real
-- name    : NemytskiiLebesgue.IsCaratheodory.nemytskii_seqContinuous_of_memLp_of_growth_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:13.109448+00:00
-- url     : https://prove2.me/theorems/1545224c-e9fb-45ff-a461-e38be30d595f
-- title:
--   Is Caratheodory: nemytskii seq Continuous of mem Lp of growth real
-- statement:
--   The Is Caratheodory construction uses the nemytskii seq Continuous of mem Lp of growth real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Continuity.lean#L436-L450
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Continuity.lean#L436-L450

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

theorem NemytskiiLebesgue.IsCaratheodory.nemytskii_seqContinuous_of_memLp_of_growth_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {uₙ : ℕ → Ω → ℝ^m} (huₙ : ∀ n : ℕ, MemLp (uₙ n) p μ)
    {u : Ω → ℝ^m} (hup : MemLp u p μ)
    (huuₙ : uₙ.NemytskiiConvergesTo u p μ) :
    (fun n : ℕ => fun ω : Ω => f ω (uₙ n ω)).NemytskiiConvergesTo (fun ω : Ω => f ω (u ω)) q μ := by sorry
