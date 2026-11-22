-- Prove2me | Theorems.Thm_NemytskiiLebesgue_ae_eq_of_ae_nemytskii_eq_nemytskii_of_ae_all_sub_inner_sub_ge
-- name    : NemytskiiLebesgue.ae_eq_of_ae_nemytskii_eq_nemytskii_of_ae_all_sub_inner_sub_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:51.352879+00:00
-- url     : https://prove2.me/theorems/816f66df-02a7-4f6b-b54f-5ad9a489a3bd
-- title:
--   Nemytskii Lebesgue: ae eq of ae nemytskii eq nemytskii of ae all sub inner sub ge
-- statement:
--   The Nemytskii Lebesgue construction uses the ae eq of ae nemytskii eq nemytskii of ae all sub inner sub ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L290-L305
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Vitali.lean#L290-L305

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal RealInnerProductSpace Topology

theorem NemytskiiLebesgue.ae_eq_of_ae_nemytskii_eq_nemytskii_of_ae_all_sub_inner_sub_ge
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : Ω → E → E} {p : ℝ} {C₂ : ℝ} (hC₂ : 0 < C₂)
    (hfCp : ∀ᵐ ω ∂μ, ∀ ξ η : E, ⟪f ω ξ - f ω η, ξ - η⟫ ≥ C₂ * ‖ξ - η‖ ^ p)
    {u v : Ω → E} (huv : (fun ω : Ω => f ω (u ω)) =ᵐ[μ] (fun ω : Ω => f ω (v ω))) :
    u =ᵐ[μ] v := by sorry
