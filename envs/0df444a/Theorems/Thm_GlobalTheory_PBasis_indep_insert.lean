-- Prove2me | Theorems.Thm_GlobalTheory_PBasis_indep_insert
-- name    : GlobalTheory.PBasis.indep_insert
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:39:08.800368+00:00
-- url     : https://prove2.me/theorems/04d30c8d-608c-45c8-bc5f-f2b7d1e83ebb
-- title:
--   PBasis: indep insert
-- statement:
--   The PBasis construction uses the indep insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GraphRingMono.lean#L77-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GraphRingMono.lean#L77-L138

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

theorem GlobalTheory.PBasis.indep_insert {p : ℕ} (hp : p.Prime) (h0 : (p : k) = 0) {B : Set k} (hB : Indep p B) {a : k}
    (ha : a ∉ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)) : Indep p (insert a B) := by sorry
