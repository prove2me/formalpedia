-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_trKer_apply
-- name    : GlobalTheory.LatPair.trKer_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:15.628609+00:00
-- url     : https://prove2.me/theorems/6ae127e8-5961-4d0b-99d0-d3a35c0eb20a
-- title:
--   Lat Pair: tr Ker apply
-- statement:
--   The Lat Pair construction uses the tr Ker apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L105-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L105-L105

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)

theorem GlobalTheory.LatPair.trKer_apply (L : Submodule 𝒪[k] (n → k)) : trKer L φ = ∑ P ∈ withKer L, φ P := by sorry
