-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Da_apply
-- name    : GlobalTheory.LatPair.Da_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:58:47.877723+00:00
-- url     : https://prove2.me/theorems/3c13b5ed-14df-4114-8eae-b40856ad54db
-- title:
--   Lat Pair: Da apply
-- statement:
--   The Lat Pair construction uses the Da apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L113-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L113-L114

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
open Classical

theorem GlobalTheory.LatPair.Da_apply (a : 𝓀[k]) (P₁ : Pair k n) :
    Da q a φ P₁ = ∑ P ∈ withLat P₁.ker with cross q P₁ P = a, φ P := by sorry
