-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_maps_stdLat_iff
-- name    : GlobalTheory.LatPair.maps_stdLat_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:22.427137+00:00
-- url     : https://prove2.me/theorems/1e0715c2-dafc-48cb-a9e4-85ebb78f5efc
-- title:
--   Lat Pair: maps std Lat iff
-- statement:
--   The Lat Pair construction uses the maps std Lat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactMapsPair.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactMapsPair.lean#L38-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
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
open SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable [Fintype n] [Fintype n']
omit [Fintype n] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.LatPair.maps_stdLat_iff {x : Matrix n n' k} :
    (∀ y ∈ stdLat k n', x *ᵥ y ∈ stdLat k n) ↔ ∀ i j, x i j ∈ 𝒪[k] := by sorry
