-- Prove2me | Theorems.Thm_GlobalTheory_signedLength_smul_self_of_addVal_eq
-- name    : GlobalTheory.signedLength_smul_self_of_addVal_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:20:39.300411+00:00
-- url     : https://prove2.me/theorems/1822ae6a-40e7-4e76-b3c3-74219ae9d675
-- title:
--   Global Theory: signed Length smul self of add Val eq
-- statement:
--   The Global Theory construction uses the signed Length smul self of add Val eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthQuotientMaximalIdealPowSmulTop.lean#L112-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthQuotientMaximalIdealPowSmulTop.lean#L112-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthQuotientMaximalIdealPowSmulTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module.IsTorsionFree R V]
  {A : Submodule R V}

theorem GlobalTheory.signedLength_smul_self_of_addVal_eq (hA : A.FG) {a : R} {n : ℕ} (hn : addVal R a = n) :
    signedLength A (a • A) = (n : ℤ) * (Module.finrank R A : ℤ) := by sorry
