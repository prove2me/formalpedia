-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_resChar_residue
-- name    : GlobalTheory.LatPair.resChar_residue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:06.371743+00:00
-- url     : https://prove2.me/theorems/0fde362f-ac56-4dd2-a0f8-b20a39f96c28
-- title:
--   Lat Pair: res Char residue
-- statement:
--   The Lat Pair construction uses the res Char residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L287-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L287-L289

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

theorem GlobalTheory.LatPair.resChar_residue {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (q : Unif k) (s : 𝒪[k]) :
    resChar ψ hψ q (residue 𝒪[k] s) = ψ (q.inv * s) := by sorry
