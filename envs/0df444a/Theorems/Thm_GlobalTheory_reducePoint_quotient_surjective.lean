-- Prove2me | Theorems.Thm_GlobalTheory_reducePoint_quotient_surjective
-- name    : GlobalTheory.reducePoint_quotient_surjective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:41:57.246428+00:00
-- url     : https://prove2.me/theorems/64921e5d-c9d1-4f3b-b629-16f9a44eaaf8
-- title:
--   Global Theory: reduce Point quotient surjective
-- statement:
--   The Global Theory construction uses the reduce Point quotient surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L149-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L149-L178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (B : Type u) [CommRing B] [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
  (s : Spec (.of B) ⟶ S)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (B : Type u) [CommRing B] [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
  (s : Spec (.of B) ⟶ S)

theorem GlobalTheory.reducePoint_quotient_surjective [Smooth f] :
    Function.Surjective (_root_.GlobalTheory.reducePoint f (CommRingCat.ofHom (Ideal.Quotient.mk I)) s) := by sorry
