-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_maps_smul
-- name    : GlobalTheory.LatPair.maps_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:00:14.33895+00:00
-- url     : https://prove2.me/theorems/2a581c0a-9cc9-4210-a1ae-4b962b839094
-- title:
--   Lat Pair: maps smul
-- statement:
--   The Lat Pair construction uses the maps smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L363-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L363-L367

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
variable [Fintype n']
variable {P : Pair k n'} {Q : Pair k n} {x : Matrix n n' k}
variable [DecidableEq n'] [Fintype n] [DecidableEq n]

theorem GlobalTheory.LatPair.maps_smul (g : GL n' k) (h : GL n k) : Maps (g • P) (h • Q) x ↔ Maps P Q ((h⁻¹ : GL n k).val * x * g.val) := by sorry
