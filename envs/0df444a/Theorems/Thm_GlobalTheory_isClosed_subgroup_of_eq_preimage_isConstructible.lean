-- Prove2me | Theorems.Thm_GlobalTheory_isClosed_subgroup_of_eq_preimage_isConstructible
-- name    : GlobalTheory.isClosed_subgroup_of_eq_preimage_isConstructible
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:58.061324+00:00
-- url     : https://prove2.me/theorems/334c4589-73f6-466a-be06-a94b7eacb435
-- title:
--   Global Theory: is Closed subgroup of eq preimage is Constructible
-- statement:
--   The Global Theory construction uses the is Closed subgroup of eq preimage is Constructible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L74-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L74-L81

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

theorem GlobalTheory.isClosed_subgroup_of_eq_preimage_isConstructible (H : Subgroup G) {f : G → Z}
    (hf : Continuous f) {C : Set Z} (hC : IsConstructible C) (hH : (H : Set G) = f ⁻¹' C) :
    IsClosed (H : Set G) := by sorry
