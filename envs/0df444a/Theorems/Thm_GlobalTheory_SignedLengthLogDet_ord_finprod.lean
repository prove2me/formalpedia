-- Prove2me | Theorems.Thm_GlobalTheory_SignedLengthLogDet_ord_finprod
-- name    : GlobalTheory.SignedLengthLogDet.ord_finprod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:12:32.42226+00:00
-- url     : https://prove2.me/theorems/8d7410e8-b094-4b22-98e7-9f20b34bcfb7
-- title:
--   Signed Length Log Det: ord finprod
-- statement:
--   The Signed Length Log Det construction uses the ord finprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthEqLogOrdFracDet.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthEqLogOrdFracDet.lean#L9-L17

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthEqLogOrdFracDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.SignedLengthLogDet
open Module

theorem GlobalTheory.SignedLengthLogDet.ord_finprod {R : Type*} [CommRing R] [IsDomain R] {ι : Type*} (s : Finset ι)
    (c : ι → R) (hc : ∀ i, c i ≠ 0) :
    Ring.ord R (∏ i ∈ s, c i) = ∑ i ∈ s, Ring.ord R (c i) := by sorry
