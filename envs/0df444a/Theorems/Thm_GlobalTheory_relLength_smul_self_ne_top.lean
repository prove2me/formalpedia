-- Prove2me | Theorems.Thm_GlobalTheory_relLength_smul_self_ne_top
-- name    : GlobalTheory.relLength_smul_self_ne_top
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:16:45.431965+00:00
-- url     : https://prove2.me/theorems/d0ff1af5-d17c-4fa1-8288-e264a0009de9
-- title:
--   Global Theory: rel Length smul self ne top
-- statement:
--   The Global Theory construction uses the rel Length smul self ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthQuotientMaximalIdealPowSmulTop.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthQuotientMaximalIdealPowSmulTop.lean#L102-L105

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

theorem GlobalTheory.relLength_smul_self_ne_top (hA : A.FG) {a : R} (ha : a ≠ 0) :
    relLength A (a • A) ≠ ⊤ := by sorry
