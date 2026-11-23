-- Prove2me | Theorems.Thm_GlobalTheory_PBasis_map_graphRing
-- name    : GlobalTheory.PBasis.map_graphRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:21.463845+00:00
-- url     : https://prove2.me/theorems/63387f18-e444-4905-ae0a-6e69a2fbc2f7
-- title:
--   PBasis: map graph Ring
-- statement:
--   The PBasis construction uses the map graph Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GraphRingMono.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GraphRingMono.lean#L20-L26

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

theorem GlobalTheory.PBasis.map_graphRing (p : ℕ) {Q : Type} [CommRing Q] (f : k →+* Q) (g : k → Q) (B : Set k) :
    (graphRing p f g B).map (RingHom.fst k Q) =
      Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) := by sorry
