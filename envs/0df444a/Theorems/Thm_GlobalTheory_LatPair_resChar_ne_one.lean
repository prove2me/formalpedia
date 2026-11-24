-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_resChar_ne_one
-- name    : GlobalTheory.LatPair.resChar_ne_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:22.602557+00:00
-- url     : https://prove2.me/theorems/2a618fc1-4658-4521-a916-0f56a0de5e1c
-- title:
--   Lat Pair: res Char ne one
-- statement:
--   The Lat Pair construction uses the res Char ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L297-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L297-L309

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
open SplitWeil

theorem GlobalTheory.LatPair.resChar_ne_one {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (q : Unif k) : resChar ψ hψ q ≠ 1 := by sorry
