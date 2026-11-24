-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_sum_withKer_smul
-- name    : GlobalTheory.LatPair.sum_withKer_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:28.699643+00:00
-- url     : https://prove2.me/theorems/83faa6df-88bb-40df-8f4e-9d0bbd711f95
-- title:
--   Lat Pair: sum with Ker smul
-- statement:
--   The Lat Pair construction uses the sum with Ker smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L166-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L166-L168

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
variable [Fintype n] [DecidableEq n]

theorem GlobalTheory.LatPair.sum_withKer_smul {A : Type*} [AddCommMonoid A] (g : GL n k) (L : Submodule 𝒪[k] (n → k)) (F : Pair k n → A) :
    ∑ P ∈ withKer (g • L), F P = ∑ P ∈ withKer L, F (g • P) := by sorry
