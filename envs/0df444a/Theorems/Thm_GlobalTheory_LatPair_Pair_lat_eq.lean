-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Pair_lat_eq
-- name    : GlobalTheory.LatPair.Pair.lat_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:58:34.296272+00:00
-- url     : https://prove2.me/theorems/7d0f99b4-45a0-405f-ae18-638a9509670f
-- title:
--   Pair: lat eq
-- statement:
--   The Pair construction uses the lat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L142-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L142-L146

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
open GlobalTheory.LatPair.Pair
variable {P Q : Pair k n} {x y e : n → k} {a b : 𝓀[k]}

theorem GlobalTheory.LatPair.Pair.lat_eq (he : P.HasVal e 1) : P.lat = P.ker ⊔ Submodule.span 𝒪[k] {e} := by sorry
