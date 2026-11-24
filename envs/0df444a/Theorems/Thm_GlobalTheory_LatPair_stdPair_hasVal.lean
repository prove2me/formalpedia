-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_stdPair_hasVal
-- name    : GlobalTheory.LatPair.stdPair_hasVal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:17.548812+00:00
-- url     : https://prove2.me/theorems/32fbed08-bbe9-4d9d-9c2d-5399f04b9b8a
-- title:
--   Lat Pair: std Pair has Val
-- statement:
--   The Lat Pair construction uses the std Pair has Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L689-L691
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L689-L691

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
variable [Fintype n]

theorem GlobalTheory.LatPair.stdPair_hasVal {i : n} {x : n → k} {a : 𝓀[k]} :
    (stdPair k i).HasVal x a ↔ ∃ h : ∀ j, x j ∈ 𝒪[k], residue 𝒪[k] ⟨x i, h i⟩ = a := by sorry
