-- Prove2me | Theorems.Thm_GlobalTheory_HopfQuot_ev_mem_equalizer
-- name    : GlobalTheory.HopfQuot.ev_mem_equalizer
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:50.029076+00:00
-- url     : https://prove2.me/theorems/0aae5a48-7674-4f2e-9417-a8af3df08ca8
-- title:
--   Hopf Quot: ev mem equalizer
-- statement:
--   The Hopf Quot construction uses the ev mem equalizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L226-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L226-L254

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {R Λ B : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
  (ρ : B →ₐ[R] B ⊗[R] Λ)

theorem GlobalTheory.HopfQuot.ev_mem_equalizer
    (hassoc : ∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) =
      (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b))
    (l : Λ →ₗ[R] R) (hl : ∀ x, ev Λ l (Coalgebra.comul x) = algebraMap R Λ (l x)) (b : B) :
    ev B l (ρ b) ∈ AlgHom.equalizer ρ
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) := by sorry
