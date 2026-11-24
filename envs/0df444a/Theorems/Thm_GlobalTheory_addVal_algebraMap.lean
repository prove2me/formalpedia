-- Prove2me | Theorems.Thm_GlobalTheory_addVal_algebraMap
-- name    : GlobalTheory.addVal_algebraMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:13:10.594848+00:00
-- url     : https://prove2.me/theorems/66919c22-23e1-462c-8f2c-255367d61c69
-- title:
--   Global Theory: add Val algebra Map
-- statement:
--   The Global Theory construction uses the add Val algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean#L123-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean#L123-L132

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

theorem GlobalTheory.addVal_algebraMap (x : R) :
    addVal S (algebraMap R S x) = addVal R x * ((maximalIdeal S).ramificationIdx R : ℕ) := by sorry
