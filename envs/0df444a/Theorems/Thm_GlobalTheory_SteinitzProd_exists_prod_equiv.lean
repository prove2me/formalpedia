-- Prove2me | Theorems.Thm_GlobalTheory_SteinitzProd_exists_prod_equiv
-- name    : GlobalTheory.SteinitzProd.exists_prod_equiv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:22:13.235802+00:00
-- url     : https://prove2.me/theorems/42c66456-cdc1-4f90-ad6e-e7e4954ccaeb
-- title:
--   Steinitz Prod: exists prod equiv
-- statement:
--   The Steinitz Prod construction uses the exists prod equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SteinitzPiIdealsLinearEquivOfClassGroupProd.lean#L54-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SteinitzPiIdealsLinearEquivOfClassGroupProd.lean#L54-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SteinitzPiIdealsLinearEquivOfClassGroupProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SteinitzProd
variable {R : Type} [CommRing R] [IsDedekindDomain R]

theorem GlobalTheory.SteinitzProd.exists_prod_equiv (I J : (Ideal R)⁰) :
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ClassGroup.mk0 I * ClassGroup.mk0 J ∧
      Nonempty ((↥(I : Ideal R) × ↥(J : Ideal R)) ≃ₗ[R] (R × ↥(L : Ideal R))) := by sorry
