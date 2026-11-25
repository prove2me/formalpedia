-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_genSubrep_le
-- name    : GroundTheory.Automorphic.RestrictedTensor.genSubrep_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:33:32.23696+00:00
-- url     : https://prove2.me/theorems/4864d231-9a73-4bbc-b3df-c7595ef619d1
-- title:
--   Restricted Tensor: gen Subrep le
-- statement:
--   The Restricted Tensor construction uses the gen Subrep le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/LocalComponent.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/LocalComponent.lean#L37-L41

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
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
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {σ : Representation ℂ L V}

theorem GroundTheory.Automorphic.RestrictedTensor.genSubrep_le {N : Submodule ℂ V} {X : Subrepresentation σ} (h : N ≤ X.toSubmodule) :
    (genSubrep σ N).toSubmodule ≤ X.toSubmodule := by sorry
