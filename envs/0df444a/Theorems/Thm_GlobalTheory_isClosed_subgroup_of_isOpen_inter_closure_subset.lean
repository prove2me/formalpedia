-- Prove2me | Theorems.Thm_GlobalTheory_isClosed_subgroup_of_isOpen_inter_closure_subset
-- name    : GlobalTheory.isClosed_subgroup_of_isOpen_inter_closure_subset
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:57:03.091871+00:00
-- url     : https://prove2.me/theorems/c6b15ef9-4ca6-46f5-81d6-58272b5f4209
-- title:
--   Global Theory: is Closed subgroup of is Open inter closure subset
-- statement:
--   The Global Theory construction uses the is Closed subgroup of is Open inter closure subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L59-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L59-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory
variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] [ContinuousInv G]

theorem GlobalTheory.isClosed_subgroup_of_isOpen_inter_closure_subset (H : Subgroup G) {V : Set G}
    (hV : IsOpen V) (hVH : V ∩ closure (H : Set G) ⊆ H) (hne : (V ∩ closure (H : Set G)).Nonempty) :
    IsClosed (H : Set G) := by sorry
