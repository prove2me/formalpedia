-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_sum_withLat
-- name    : GlobalTheory.LatPair.sum_withLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:56.587307+00:00
-- url     : https://prove2.me/theorems/c2ac8538-e3e5-41b5-91f0-0585ef6947a7
-- title:
--   Lat Pair: sum with Lat
-- statement:
--   The Lat Pair construction uses the sum with Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L471-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L471-L476

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

theorem GlobalTheory.LatPair.sum_withLat {M : Type*} [AddCommMonoid M] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    [Fintype {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}] (F : Pair k n → M) :
    ∑ P ∈ withLat L, F P = ∑ f, F (ofDual L f) := by sorry
