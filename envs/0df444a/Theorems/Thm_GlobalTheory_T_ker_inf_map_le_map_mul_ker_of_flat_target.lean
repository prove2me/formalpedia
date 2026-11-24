-- Prove2me | Theorems.Thm_GlobalTheory_T_ker_inf_map_le_map_mul_ker_of_flat_target
-- name    : GlobalTheory.T.ker_inf_map_le_map_mul_ker_of_flat_target
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:50:59.794503+00:00
-- url     : https://prove2.me/theorems/27678c68-96b2-4f89-b5dc-f7a4e175edc0
-- title:
--   T: ker inf map le map mul ker of flat target
-- statement:
--   The T construction uses the ker inf map le map mul ker of flat target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerInfMapLeMapMulKerOfFlatTargetStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerInfMapLeMapMulKerOfFlatTargetStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerInfMapLeMapMulKerOfFlatTarget
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerInfMapLeMapMulKerOfFlatTargetStatement
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

theorem GlobalTheory.T.ker_inf_map_le_map_mul_ker_of_flat_target : ∀ (B P A : Type) [CommRing B] [CommRing P] [CommRing A] [Algebra B P] [Algebra B A] [Module.Flat B A] (Ψ : P →ₐ[B] A), Function.Surjective Ψ → ∀ I : Ideal B, RingHom.ker Ψ ⊓ I.map (algebraMap B P) ≤ I.map (algebraMap B P) * RingHom.ker Ψ := by sorry
