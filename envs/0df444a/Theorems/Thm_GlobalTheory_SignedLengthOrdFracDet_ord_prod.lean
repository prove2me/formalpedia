-- Prove2me | Theorems.Thm_GlobalTheory_SignedLengthOrdFracDet_ord_prod
-- name    : GlobalTheory.SignedLengthOrdFracDet.ord_prod
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:12:32.809278+00:00
-- url     : https://prove2.me/theorems/30198d1e-ba9b-4fb9-a0ce-ea594c3b8272
-- title:
--   Signed Length Ord Frac Det: ord prod
-- statement:
--   The Signed Length Ord Frac Det construction uses the ord prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthSpanEqOrdFracDet.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthSpanEqOrdFracDet.lean#L7-L14

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthSpanEqOrdFracDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SignedLengthOrdFracDet
open Module Submodule

theorem GlobalTheory.SignedLengthOrdFracDet.ord_prod {R : Type*} [CommRing R] [IsDomain R] {ι : Type*} (s : Finset ι) (c : ι → R)
    (hc : ∀ i, c i ≠ 0) : Ring.ord R (∏ i ∈ s, c i) = ∑ i ∈ s, Ring.ord R (c i) := by sorry
