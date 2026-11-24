-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Pair_ker_le
-- name    : GlobalTheory.LatPair.Pair.ker_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:58:43.622327+00:00
-- url     : https://prove2.me/theorems/260bd8ba-1064-4cd4-9a4c-7554c07ed316
-- title:
--   Pair: ker le
-- statement:
--   The Pair construction uses the ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L106-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L106-L106

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

theorem GlobalTheory.LatPair.Pair.ker_le (P : Pair k n) : P.ker ≤ P.lat := by sorry
