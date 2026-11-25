-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactRep_isFullyInvariant_sSup
-- name    : GroundTheory.Automorphic.CompactRep.isFullyInvariant_sSup
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:29:14.2126+00:00
-- url     : https://prove2.me/theorems/6c0a8437-c430-4c8a-a32a-c070a7233623
-- title:
--   Compact Rep: is Fully Invariant s Sup
-- statement:
--   The Compact Rep construction uses the is Fully Invariant s Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L102-L104

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CompactRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.CompactRep
open Module Set
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {X : Type*} [AddCommGroup X] [Module ℂ X]
variable {σ : Representation ℂ K X}
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]

theorem GroundTheory.Automorphic.CompactRep.isFullyInvariant_sSup {s : Set (Submodule R M)} (h : ∀ m ∈ s, m.IsFullyInvariant) :
    (sSup s).IsFullyInvariant := by sorry
