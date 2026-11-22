-- Prove2me | Theorems.Thm_NemytskiiLebesgue_hasFDerivAt_outR1_outR1nested
-- name    : NemytskiiLebesgue.hasFDerivAt_outR1_outR1nested
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:26.096553+00:00
-- url     : https://prove2.me/theorems/d00f9ce2-d6a6-45ea-b3d3-d23113fe2b8a
-- title:
--   Nemytskii Lebesgue: has FDeriv At out R1 out R1nested
-- statement:
--   The Nemytskii Lebesgue construction uses the has FDeriv At out R1 out R1nested property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L88-L95
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L88-L95

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso
public import Definitions.Def_LeanPool_NemytskiiLebesgue_IntegralFunctional
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal

theorem NemytskiiLebesgue.hasFDerivAt_outR1_outR1nested
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f : Ω → ℝ^m → ℝ} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)}
    (hff' : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ) :
    ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (NemytskiiLebesgue.outR1 f ω) (NemytskiiLebesgue.outR1nested f'
      ω ξ) ξ := by sorry
