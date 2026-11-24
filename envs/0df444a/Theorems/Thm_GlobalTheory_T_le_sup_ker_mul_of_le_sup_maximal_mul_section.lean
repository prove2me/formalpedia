-- Prove2me | Theorems.Thm_GlobalTheory_T_le_sup_ker_mul_of_le_sup_maximal_mul_section
-- name    : GlobalTheory.T.le_sup_ker_mul_of_le_sup_maximal_mul_section
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:51:23.302568+00:00
-- url     : https://prove2.me/theorems/a85c1a8b-8874-486f-9707-0c93372896d8
-- title:
--   T: le sup ker mul of le sup maximal mul section
-- statement:
--   The T construction uses the le sup ker mul of le sup maximal mul section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeSupKerMulOfLeSupMaximalMulSectionStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeSupKerMulOfLeSupMaximalMulSectionStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeSupKerMulOfLeSupMaximalMulSection
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeSupKerMulOfLeSupMaximalMulSectionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.le_sup_ker_mul_of_le_sup_maximal_mul_section : ∀ (O P : Type) [CommRing O] [IsLocalRing O] [CommRing P] [Algebra O P] (η : P →ₐ[O] O) (J S : Ideal P), J.FG → J ≤ S ⊔ (IsLocalRing.maximalIdeal O).comap η * J → J ≤ S ⊔ RingHom.ker η * J := by sorry
