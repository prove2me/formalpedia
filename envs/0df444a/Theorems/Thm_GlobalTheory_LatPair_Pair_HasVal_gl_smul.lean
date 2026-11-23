-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Pair_HasVal_gl_smul
-- name    : GlobalTheory.LatPair.Pair.HasVal.gl_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:09:20.141675+00:00
-- url     : https://prove2.me/theorems/0f377fce-f382-4937-b607-2f38a9921f0e
-- title:
--   Has Val: gl smul
-- statement:
--   The Has Val construction uses the gl smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L564-L565
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L564-L565

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
variable [Fintype n] [DecidableEq n]
open GlobalTheory.LatPair.Pair

theorem GlobalTheory.LatPair.Pair.HasVal.gl_smul {P : Pair k n} {x : n → k} {a : 𝓀[k]} (h : P.HasVal x a) (g : GL n k) :
    (g • P).HasVal (g • x) a := by sorry
