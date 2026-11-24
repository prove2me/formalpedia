-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_conj_resChar
-- name    : GlobalTheory.LatPair.conj_resChar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:56.646015+00:00
-- url     : https://prove2.me/theorems/425dc692-84b0-42a8-bc40-c4c2a214dc34
-- title:
--   Lat Pair: conj res Char
-- statement:
--   The Lat Pair construction uses the conj res Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L291-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L291-L295

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

theorem GlobalTheory.LatPair.conj_resChar {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (q : Unif k) (a : 𝓀[k]) :
    (starRingEnd ℂ) (resChar ψ hψ q a) = resChar ψ hψ q (-a) := by sorry
