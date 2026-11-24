-- Prove2me | Theorems.Thm_GlobalTheory_SignedLengthMapLogDet_length_coker_eq_ord_det
-- name    : GlobalTheory.SignedLengthMapLogDet.length_coker_eq_ord_det
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:12:55.798887+00:00
-- url     : https://prove2.me/theorems/aa91ab19-797f-4810-b391-b569469fb51c
-- title:
--   Signed Length Map Log Det: length coker eq ord det
-- statement:
--   The Signed Length Map Log Det construction uses the length coker eq ord det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthMapEqLogOrdFracDet.lean#L22-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthMapEqLogOrdFracDet.lean#L22-L50

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthMapEqLogOrdFracDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.SignedLengthMapLogDet
open Module
variable {R : Type*} [CommRing R] [IsDomain R]

theorem GlobalTheory.SignedLengthMapLogDet.length_coker_eq_ord_det [IsPrincipalIdealRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = Ring.ord R (LinearMap.det f) := by sorry
