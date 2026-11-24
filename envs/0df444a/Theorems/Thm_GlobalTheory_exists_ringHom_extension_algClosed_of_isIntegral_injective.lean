-- Prove2me | Theorems.Thm_GlobalTheory_exists_ringHom_extension_algClosed_of_isIntegral_injective
-- name    : GlobalTheory.exists_ringHom_extension_algClosed_of_isIntegral_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:41:11.937087+00:00
-- url     : https://prove2.me/theorems/b7aac414-bfef-4969-ae44-d4bd071b002c
-- title:
--   Global Theory: exists ring Hom extension alg Closed of is Integral injective
-- statement:
--   The Global Theory construction uses the exists ring Hom extension alg Closed of is Integral injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRootMapMinpolyIffExistsRingHomExtension.lean#L6-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRootMapMinpolyIffExistsRingHomExtension.lean#L6-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomCompAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRootMapMinpolyIffExistsRingHomExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.exists_ringHom_extension_algClosed_of_isIntegral_injective {R S K : Type*} [CommRing R] [CommRing S] [Field K] [IsAlgClosed K]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (ψ : R →+* K) : ∃ x : S →+* K, x.comp (algebraMap R S) = ψ := by sorry
