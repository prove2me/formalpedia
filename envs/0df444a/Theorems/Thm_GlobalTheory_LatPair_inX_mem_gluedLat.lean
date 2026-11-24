-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_inX_mem_gluedLat
-- name    : GlobalTheory.LatPair.inX_mem_gluedLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:55.832926+00:00
-- url     : https://prove2.me/theorems/7b0f0e60-988c-44b7-897d-6f4c7dd46683
-- title:
--   Lat Pair: in X mem glued Lat
-- statement:
--   The Lat Pair construction uses the in X mem glued Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L516-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L516-L524

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {c : ℕ}

theorem GlobalTheory.LatPair.inX_mem_gluedLat {q : Unif k} {p : ℕ} (h1 : 1 ≤ p) (hp : p ≤ c) {L : Submodule 𝒪[k] (n → k)} {f x : n → k} :
    inX k n c x ∈ gluedLat q c p L f ↔ x ∈ L := by sorry
