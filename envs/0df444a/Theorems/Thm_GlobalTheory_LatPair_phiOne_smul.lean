-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_phiOne_smul
-- name    : GlobalTheory.LatPair.phiOne_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:01.242871+00:00
-- url     : https://prove2.me/theorems/fa1185c8-25ee-4a45-8ec4-8da5f585b6d6
-- title:
--   Lat Pair: phi One smul
-- statement:
--   The Lat Pair construction uses the phi One smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L369-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L369-L372

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

theorem GlobalTheory.LatPair.phiOne_smul (g : GL n' k) (h : GL n k) :
    phiOne (g • P) (h • Q) x = phiOne P Q ((h⁻¹ : GL n k).val * x * g.val) := by sorry
