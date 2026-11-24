-- Prove2me | Theorems.Thm_GlobalTheory_InjectiveAlgebraHomExistence_exists_algHom_of_injective
-- name    : GlobalTheory.InjectiveAlgebraHomExistence.exists_algHom_of_injective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:11.839963+00:00
-- url     : https://prove2.me/theorems/e1733b0f-30fd-4298-8244-077429458b0a
-- title:
--   Injective Algebra Hom Existence: exists alg Hom of injective
-- statement:
--   The Injective Algebra Hom Existence construction uses the exists alg Hom of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRingHomCompAlgebraMapEq.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRingHomCompAlgebraMapEq.lean#L7-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomCompAlgebraMapEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.InjectiveAlgebraHomExistence

theorem GlobalTheory.InjectiveAlgebraHomExistence.exists_algHom_of_injective {A : Type u_1} {B : Type u_2} {K : Type u_3}
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field K] [IsAlgClosed K]
    [Algebra A B] [Algebra A K] [Algebra.IsIntegral A B]
    (hB : Function.Injective (algebraMap A B)) (hK : Function.Injective (algebraMap A K)) :
    Nonempty (B →ₐ[A] K) := by sorry
