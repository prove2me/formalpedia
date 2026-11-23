-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_cross_smul
-- name    : GlobalTheory.LatPair.cross_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:51.466411+00:00
-- url     : https://prove2.me/theorems/1b49d09e-de07-4852-b8a9-20d04fe8c435
-- title:
--   Lat Pair: cross smul
-- statement:
--   The Lat Pair construction uses the cross smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L579-L583
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L579-L583

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

theorem GlobalTheory.LatPair.cross_smul (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) (g : GL n k) :
    cross q (g • P₁) (g • P) = cross q P₁ P := by sorry
