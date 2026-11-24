-- Prove2me | Theorems.Thm_GlobalTheory_SteinitzProd_exists_pi_equiv
-- name    : GlobalTheory.SteinitzProd.exists_pi_equiv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:22:23.232826+00:00
-- url     : https://prove2.me/theorems/09d9e537-90ae-44a7-9455-afb13c68cba1
-- title:
--   Steinitz Prod: exists pi equiv
-- statement:
--   The Steinitz Prod construction uses the exists pi equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SteinitzPiIdealsLinearEquivOfClassGroupProd.lean#L87-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SteinitzPiIdealsLinearEquivOfClassGroupProd.lean#L87-L97

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

theorem GlobalTheory.SteinitzProd.exists_pi_equiv {ι : Type} [Fintype ι] {n : ℕ} (e : ι ≃ Fin (n + 1))
    (I : ι → (Ideal R)⁰) :
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ∏ i, ClassGroup.mk0 (I i) ∧
      Nonempty (((i : ι) → ↥(I i : Ideal R)) ≃ₗ[R] (↥(L : Ideal R) × (Fin n → R))) := by sorry
