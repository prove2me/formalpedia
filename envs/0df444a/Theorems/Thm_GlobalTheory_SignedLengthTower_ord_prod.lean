-- Prove2me | Theorems.Thm_GlobalTheory_SignedLengthTower_ord_prod
-- name    : GlobalTheory.SignedLengthTower.ord_prod
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:12:51.719377+00:00
-- url     : https://prove2.me/theorems/59d84bfa-5f8a-43da-9c34-bf96c9fb6413
-- title:
--   Signed Length Tower: ord prod
-- statement:
--   The Signed Length Tower construction uses the ord prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RelLengthSpanMatrix.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RelLengthSpanMatrix.lean#L26-L33

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.SignedLengthTower

theorem GlobalTheory.SignedLengthTower.ord_prod {R ι : Type*} [CommRing R] [IsDomain R] (s : Finset ι) (d : ι → R)
    (hd : ∀ i, d i ≠ 0) : Ring.ord R (∏ i ∈ s, d i) = ∑ i ∈ s, Ring.ord R (d i) := by sorry
