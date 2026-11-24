-- Prove2me | Theorems.Thm_GlobalTheory_ker_inf_map_le_map_mul_ker_of_flat
-- name    : GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:02:42.403149+00:00
-- url     : https://prove2.me/theorems/19fa4f10-8a69-43cf-9763-3608d5be4067
-- title:
--   Global Theory: ker inf map le map mul ker of flat
-- statement:
--   The Global Theory construction uses the ker inf map le map mul ker of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerInfMapLeMapMulKerOfFlatTarget.lean#L16-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerInfMapLeMapMulKerOfFlatTarget.lean#L16-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerInfMapLeMapMulKerOfFlatTarget
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

theorem GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat :
    ∀ (B P A : Type) [CommRing B] [CommRing P] [CommRing A] [Algebra B P] [Algebra B A]
      [Module.Flat B A] (Ψ : P →ₐ[B] A), Function.Surjective Ψ → ∀ I : Ideal B,
      RingHom.ker Ψ ⊓ I.map (algebraMap B P) ≤ I.map (algebraMap B P) * RingHom.ker Ψ := by sorry
