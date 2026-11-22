-- Prove2me | Theorems.Thm_NemytskiiLebesgue_outR1nested_norm_eq
-- name    : NemytskiiLebesgue.outR1nested_norm_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:30.844257+00:00
-- url     : https://prove2.me/theorems/2345f096-716b-4bf9-95b3-513d8e40b61d
-- title:
--   Nemytskii Lebesgue: out R1nested norm eq
-- statement:
--   The Nemytskii Lebesgue construction uses the out R1nested norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L97-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/IntegralFunctional.lean#L97-L111

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

theorem NemytskiiLebesgue.outR1nested_norm_eq
    {Ω : Type*}
    {m : ℕ}
    (f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)) (ω : Ω) (ξ : ℝ^m) :
    ‖NemytskiiLebesgue.outR1nested f' ω ξ‖ = ‖f' ω ξ‖ := by sorry
