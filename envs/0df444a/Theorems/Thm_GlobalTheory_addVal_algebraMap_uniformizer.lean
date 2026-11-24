-- Prove2me | Theorems.Thm_GlobalTheory_addVal_algebraMap_uniformizer
-- name    : GlobalTheory.addVal_algebraMap_uniformizer
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:05:46.018792+00:00
-- url     : https://prove2.me/theorems/4be6e5b5-722f-45d9-89d7-ef15757572b3
-- title:
--   Global Theory: add Val algebra Map uniformizer
-- statement:
--   The Global Theory construction uses the add Val algebra Map uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean#L116-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBaseChangeQuotientOfMapMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open IsDiscreteValuationRing hiding maximalIdeal
variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]
variable [IsLocalHom (algebraMap R S)]
variable {R}

theorem GlobalTheory.addVal_algebraMap_uniformizer {ϖ : R} (hϖ : Irreducible ϖ) :
    addVal S (algebraMap R S ϖ) = ((maximalIdeal S).ramificationIdx R : ℕ) := by sorry
