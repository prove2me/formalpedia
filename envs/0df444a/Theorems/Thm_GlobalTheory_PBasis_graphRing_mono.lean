-- Prove2me | Theorems.Thm_GlobalTheory_PBasis_graphRing_mono
-- name    : GlobalTheory.PBasis.graphRing_mono
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:38:52.516822+00:00
-- url     : https://prove2.me/theorems/9a80ed72-5ff0-4b5f-b5ca-fc718360e348
-- title:
--   PBasis: graph Ring mono
-- statement:
--   The PBasis construction uses the graph Ring mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GraphRingMono.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GraphRingMono.lean#L16-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GraphRingMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.PBasis
variable {k : Type} [Field k]

theorem GlobalTheory.PBasis.graphRing_mono (p : ℕ) {Q : Type} [CommRing Q] (f : k →+* Q) (g : k → Q) {B C : Set k}
    (h : B ⊆ C) : graphRing p f g B ≤ graphRing p f g C := by sorry
