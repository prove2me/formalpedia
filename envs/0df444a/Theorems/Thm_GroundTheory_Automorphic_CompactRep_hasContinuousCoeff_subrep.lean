-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactRep_hasContinuousCoeff_subrep
-- name    : GroundTheory.Automorphic.CompactRep.hasContinuousCoeff_subrep
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:26:37.402873+00:00
-- url     : https://prove2.me/theorems/3b96c4ff-ce3d-4f20-b0ed-127680332a04
-- title:
--   Compact Rep: has Continuous Coeff subrep
-- statement:
--   The Compact Rep construction uses the has Continuous Coeff subrep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L22-L30

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

theorem GroundTheory.Automorphic.CompactRep.hasContinuousCoeff_subrep (hσ : Representation.HasContinuousCoeff σ)
    (P : Subrepresentation σ) : Representation.HasContinuousCoeff P.toRepresentation := by sorry
