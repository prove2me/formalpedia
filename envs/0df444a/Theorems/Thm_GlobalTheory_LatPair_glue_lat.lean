-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_glue_lat
-- name    : GlobalTheory.LatPair.glue_lat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:59:19.099813+00:00
-- url     : https://prove2.me/theorems/0b875f20-29c1-43d4-b794-4af49959e18c
-- title:
--   Lat Pair: glue lat
-- statement:
--   The Lat Pair construction uses the glue lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L228-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L228-L229

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
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
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {n n' : Type*}
variable {L L' : Submodule 𝒪[k] (n → k)} {e e' : n → k}

theorem GlobalTheory.LatPair.glue_lat (h : IsGlue L e) : (glue h).lat = L ⊔ Submodule.span 𝒪[k] {e} := by sorry
