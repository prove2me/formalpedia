-- Prove2me | Theorems.Thm_GlobalTheory_exists_eval_eq_of_multiplicative_on_points
-- name    : GlobalTheory.exists_eval_eq_of_multiplicative_on_points
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:40.215687+00:00
-- url     : https://prove2.me/theorems/7b0307d7-1275-4833-8c0b-e1852e6f8947
-- title:
--   Global Theory: exists eval eq of multiplicative on points
-- statement:
--   The Global Theory construction uses the exists eval eq of multiplicative on points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEvalEqOfMultiplicativeOnPoints.lean#L121-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEvalEqOfMultiplicativeOnPoints.lean#L121-L218

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorEqZeroOfForallGeometricPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GroupLikeIntegralOfFiniteFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEvalEqOfMultiplicativeOnPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open scoped TensorProduct

theorem GlobalTheory.exists_eval_eq_of_multiplicative_on_points : ∀ (O C A : Type) [CommRing O] [IsDomain O] [Field C] [IsAlgClosed C] [Algebra O C] [IsFractionRing O C] [IsIntegrallyClosed O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Free O A], IsReduced (C ⊗[O] A) → ∀ (Δ : A →ₐ[O] A ⊗[O] A) (ε : A →ₐ[O] O) (κ : (A →ₐ[O] C) → C), (∀ x y : A →ₐ[O] C, κ ((Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)).comp Δ) = κ x * κ y) → κ ((Algebra.ofId O C).comp ε) = 1 → ∃ b : A, ∀ x : A →ₐ[O] C, x b = κ x := by sorry
