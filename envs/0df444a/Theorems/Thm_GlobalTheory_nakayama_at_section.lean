-- Prove2me | Theorems.Thm_GlobalTheory_nakayama_at_section
-- name    : GlobalTheory.nakayama_at_section
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:12:07.795891+00:00
-- url     : https://prove2.me/theorems/ce524962-5917-4fc0-b82d-07c97aa94464
-- title:
--   Global Theory: nakayama at section
-- statement:
--   The Global Theory construction uses the nakayama at section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeSupKerMulOfLeSupMaximalMulSection.lean#L6-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeSupKerMulOfLeSupMaximalMulSection.lean#L6-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeSupKerMulOfLeSupMaximalMulSection
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

theorem GlobalTheory.nakayama_at_section : ∀ (O P : Type) [CommRing O] [IsLocalRing O] [CommRing P] [Algebra O P] (η : P →ₐ[O] O) (J S : Ideal P), J.FG → J ≤ S ⊔ (IsLocalRing.maximalIdeal O).comap η * J → J ≤ S ⊔ RingHom.ker η * J := by sorry
