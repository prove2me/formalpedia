-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_gluedLat_congr
-- name    : GlobalTheory.LatPair.gluedLat_congr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:58:29.064683+00:00
-- url     : https://prove2.me/theorems/dde2960d-5727-40cc-afad-aeee8c604a9d
-- title:
--   Lat Pair: glued Lat congr
-- statement:
--   The Lat Pair construction uses the glued Lat congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L509-L514
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L509-L514

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

theorem GlobalTheory.LatPair.gluedLat_congr (q : Unif k) (c p : ℕ) {L : Submodule 𝒪[k] (n → k)} {f f' : n → k} (h : f - f' ∈ L) :
    gluedLat q c p L f = gluedLat q c p L f' := by sorry
