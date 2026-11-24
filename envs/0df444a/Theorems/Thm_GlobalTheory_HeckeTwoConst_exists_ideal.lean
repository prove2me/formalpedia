-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoConst_exists_ideal
-- name    : GlobalTheory.HeckeTwoConst.exists_ideal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:14:51.067918+00:00
-- url     : https://prove2.me/theorems/2ffe52c8-2da4-4c6a-9502-2237b6db690b
-- title:
--   Hecke Two Const: exists ideal
-- statement:
--   The Hecke Two Const construction uses the exists ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoConstantTermEqPartialZetaNegOne.lean#L13-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoConstantTermEqPartialZetaNegOne.lean#L13-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoConstantTermEqPartialZetaNegOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.HeckeTwoConst
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.HeckeTwoConst.exists_ideal (M : FractionalIdeal (𝓞 F)⁰ F) (N : Frac F) (hM : M * (N : FractionalIdeal (𝓞 F)⁰ F) = 1)
    (a : NZ M) : ∃ J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = ClassGroup.mk F N},
      ((J.1 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ a.1 * N := by sorry
