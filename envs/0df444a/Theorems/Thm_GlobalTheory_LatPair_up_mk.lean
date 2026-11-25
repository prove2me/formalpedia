-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_up_mk
-- name    : GlobalTheory.LatPair.up_mk
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:00.184684+00:00
-- url     : https://prove2.me/theorems/ec8a71f9-0a61-4f7f-8859-171c3ce67fe1
-- title:
--   Lat Pair: up mk
-- statement:
--   The Lat Pair construction uses the up mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L430-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L430-L431

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
variable (L : Submodule 𝒪[k] (n → k)) [hL : L.IsLattice k]
variable (q : Unif k)

theorem GlobalTheory.LatPair.up_mk {y : L} (hy : Red.mk L y ≠ 0) : up L q ⟨_, hy⟩ = glue (isGlue_inv_smul L q hy) := by sorry
