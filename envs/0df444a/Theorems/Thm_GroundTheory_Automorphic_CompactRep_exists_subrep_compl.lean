-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactRep_exists_subrep_compl
-- name    : GroundTheory.Automorphic.CompactRep.exists_subrep_compl
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:28:58.166955+00:00
-- url     : https://prove2.me/theorems/ec8dec3d-f433-4334-a8f0-aa61535d7280
-- title:
--   Compact Rep: exists subrep compl
-- statement:
--   The Compact Rep construction uses the exists subrep compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L32-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L32-L68

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

theorem GroundTheory.Automorphic.CompactRep.exists_subrep_compl (h : IsKFinite σ) (v : X) {Y : Subrepresentation σ}
    (hY : Y ≤ RestrictedTensor.orbitSpan σ v) :
    ∃ C : Subrepresentation σ, C ≤ RestrictedTensor.orbitSpan σ v ∧ Y ⊓ C = ⊥ ∧
      Y ⊔ C = RestrictedTensor.orbitSpan σ v := by sorry
