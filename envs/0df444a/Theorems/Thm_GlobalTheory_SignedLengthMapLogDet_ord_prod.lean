-- Prove2me | Theorems.Thm_GlobalTheory_SignedLengthMapLogDet_ord_prod
-- name    : GlobalTheory.SignedLengthMapLogDet.ord_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:13:04.998453+00:00
-- url     : https://prove2.me/theorems/6f454120-4d8f-4f79-9695-dbfe12534e86
-- title:
--   Signed Length Map Log Det: ord prod
-- statement:
--   The Signed Length Map Log Det construction uses the ord prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthMapEqLogOrdFracDet.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthMapEqLogOrdFracDet.lean#L13-L20

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

theorem GlobalTheory.SignedLengthMapLogDet.ord_prod {ι : Type*} (s : Finset ι) (a : ι → R) (ha : ∀ i, a i ≠ 0) :
    Ring.ord R (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord R (a i) := by sorry
