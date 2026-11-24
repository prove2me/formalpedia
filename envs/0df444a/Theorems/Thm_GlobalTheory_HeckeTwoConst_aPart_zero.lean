-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoConst_aPart_zero
-- name    : GlobalTheory.HeckeTwoConst.aPart_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:14:25.989281+00:00
-- url     : https://prove2.me/theorems/9f98084c-7512-4a11-ac5b-74e967745a1d
-- title:
--   Hecke Two Const: a Part zero
-- statement:
--   The Hecke Two Const construction uses the a Part zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoConstantTermEqPartialZetaNegOne.lean#L95-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoConstantTermEqPartialZetaNegOne.lean#L95-L126

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

theorem GlobalTheory.HeckeTwoConst.aPart_zero [IsTotallyReal F] (𝔞 : Frac F) (C : ClassGroup (𝓞 F)) (D : (Ideal (𝓞 F))⁰) (Za : ℂ → ℂ)
    (hD : (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F)) (hC : C * (ClassGroup.mk F 𝔞)⁻¹ = ClassGroup.mk0 D)
    (hZ : IsPartialZeta C Za) :
    aPart 𝔞 0 = ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2) ^ Module.finrank ℚ F * ((dF F : ℂ) * (nrm 𝔞 : ℂ)) ^ 2 * Za 2 := by sorry
