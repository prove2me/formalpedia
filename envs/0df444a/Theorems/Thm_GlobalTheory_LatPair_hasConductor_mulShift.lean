-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_hasConductor_mulShift
-- name    : GlobalTheory.LatPair.hasConductor_mulShift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:53.471365+00:00
-- url     : https://prove2.me/theorems/fcd10a2e-25c2-46d7-8579-01bd2f46715a
-- title:
--   Lat Pair: has Conductor mul Shift
-- statement:
--   The Lat Pair construction uses the has Conductor mul Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L311-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L311-L319

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

theorem GlobalTheory.LatPair.hasConductor_mulShift {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (u : 𝒪[k]ˣ) :
    HasConductor (ψ.mulShift ((u : 𝒪[k]) : k)) 1 := by sorry
