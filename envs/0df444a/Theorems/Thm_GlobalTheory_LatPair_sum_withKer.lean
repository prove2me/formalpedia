-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_sum_withKer
-- name    : GlobalTheory.LatPair.sum_withKer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:36.102652+00:00
-- url     : https://prove2.me/theorems/0fe3d2e7-8c0d-4c5a-83e9-1caf496a7189
-- title:
--   Lat Pair: sum with Ker
-- statement:
--   The Lat Pair construction uses the sum with Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L478-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L478-L483

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
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
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {n n' : Type*}

theorem GlobalTheory.LatPair.sum_withKer {M : Type*} [AddCommMonoid M] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (q : Unif k)
    [Fintype {x : Red L // x ≠ 0}] (F : Pair k n → M) :
    ∑ P ∈ withKer L, F P = ∑ x, F (up L q x) := by sorry
