-- Prove2me | Theorems.Thm_GlobalTheory_signedLength_smul_self
-- name    : GlobalTheory.signedLength_smul_self
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:51.577696+00:00
-- url     : https://prove2.me/theorems/c288a758-aeb4-4d20-aaec-95042e9b2ed0
-- title:
--   Global Theory: signed Length smul self
-- statement:
--   The Global Theory construction uses the signed Length smul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthQuotientMaximalIdealPowSmulTop.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthQuotientMaximalIdealPowSmulTop.lean#L118-L120

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

theorem GlobalTheory.signedLength_smul_self (hA : A.FG) {a : R} (ha : a ≠ 0) :
    signedLength A (a • A) = ((addVal R a).toNat : ℤ) * (Module.finrank R A : ℤ) := by sorry
