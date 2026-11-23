-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_quotientEquivOfMapEq_tmul
-- name    : GlobalTheory.GaloisDescent.quotientEquivOfMapEq_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:11.241864+00:00
-- url     : https://prove2.me/theorems/550e4beb-bf25-40da-8264-5a3b7ac4ee1f
-- title:
--   Galois Descent: quotient Equiv Of Map Eq tmul
-- statement:
--   The Galois Descent construction uses the quotient Equiv Of Map Eq tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/MvPolynomialIsHomogeneousComapWeighted.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/MvPolynomialIsHomogeneousComapWeighted.lean#L94-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
open Algebra.TensorProduct
variable {K L A G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]

theorem GlobalTheory.GaloisDescent.quotientEquivOfMapEq_tmul {A : Type*} [CommRing A] [Algebra K A] (I₀ : Ideal A)
    (I : Ideal (L ⊗[K] A)) (h : I₀.map (includeRight : A →ₐ[K] L ⊗[K] A) = I) (l : L) (a : A) :
    quotientEquivOfMapEq I₀ I h (l ⊗ₜ Ideal.Quotient.mk I₀ a) = Ideal.Quotient.mk I (l ⊗ₜ a) := by sorry

attribute [defeq] GlobalTheory.GaloisDescent.quotientEquivOfMapEq_tmul
