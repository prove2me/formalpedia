-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_embX_smul_gluedLat
-- name    : GlobalTheory.LatPair.embX_smul_gluedLat
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:58:24.801182+00:00
-- url     : https://prove2.me/theorems/9a8a2515-26ed-45c7-84b1-1bc9143acb22
-- title:
--   Lat Pair: emb X smul glued Lat
-- statement:
--   The Lat Pair construction uses the emb X smul glued Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L568-L578
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L568-L578

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
variable [Fintype n] [DecidableEq n]

theorem GlobalTheory.LatPair.embX_smul_gluedLat (g : GL n k) (q : Unif k) (c p : ℕ) (L : Submodule 𝒪[k] (n → k)) (f : n → k) :
    RootEx.embX c g • gluedLat q c p L f = gluedLat q c p (g • L) (g • f) := by sorry
