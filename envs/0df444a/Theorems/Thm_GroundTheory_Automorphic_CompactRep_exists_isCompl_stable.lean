-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactRep_exists_isCompl_stable
-- name    : GroundTheory.Automorphic.CompactRep.exists_isCompl_stable
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:15:32.066262+00:00
-- url     : https://prove2.me/theorems/8562913f-69cc-44a2-8c00-52aab7b6f220
-- title:
--   Compact Rep: exists is Compl stable
-- statement:
--   The Compact Rep construction uses the exists is Compl stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/CompactRep.lean#L16-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/CompactRep.lean#L16-L120

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CompactRep
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
open MeasureTheory Module Set
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  {σ : Representation ℂ K W}

theorem GroundTheory.Automorphic.CompactRep.exists_isCompl_stable (hσ : Representation.HasContinuousCoeff σ) (U : Submodule ℂ W)
    (hU : ∀ k, ∀ u ∈ U, σ k u ∈ U) :
    ∃ C : Submodule ℂ W, IsCompl U C ∧ ∀ k, ∀ c ∈ C, σ k c ∈ C := by sorry
