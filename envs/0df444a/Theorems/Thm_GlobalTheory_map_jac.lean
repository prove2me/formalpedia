-- Prove2me | Theorems.Thm_GlobalTheory_map_jac
-- name    : GlobalTheory.map_jac
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:09:42.489738+00:00
-- url     : https://prove2.me/theorems/9101be15-efea-4fac-9104-6eed3c08540e
-- title:
--   Global Theory: map jac
-- statement:
--   The Global Theory construction uses the map jac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L239-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L239-L247

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {D : ℕ}
open KaehlerDifferential
variable {R}

theorem GlobalTheory.map_jac (S B : Type*) [CommRing S] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] [IsScalarTower R S B] [SMulCommClass S A B]
    (f : Fin (D + 1) → A) :
    exteriorPowerMapOver B D (KaehlerDifferential.map R S A B) (jac R f)
      = jac S (fun i => algebraMap A B (f i)) := by sorry
