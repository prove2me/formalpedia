-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_sum_withLat_smul
-- name    : GlobalTheory.LatPair.sum_withLat_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:52.499965+00:00
-- url     : https://prove2.me/theorems/c2f20e56-bbae-4cc3-8632-28dfc1b6541e
-- title:
--   Lat Pair: sum with Lat smul
-- statement:
--   The Lat Pair construction uses the sum with Lat smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L162-L164

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

theorem GlobalTheory.LatPair.sum_withLat_smul {A : Type*} [AddCommMonoid A] (g : GL n k) (L : Submodule 𝒪[k] (n → k)) (F : Pair k n → A) :
    ∑ P ∈ withLat (g • L), F P = ∑ P ∈ withLat L, F (g • P) := by sorry
