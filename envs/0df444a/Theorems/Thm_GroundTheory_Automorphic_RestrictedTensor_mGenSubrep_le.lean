-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mGenSubrep_le
-- name    : GroundTheory.Automorphic.RestrictedTensor.mGenSubrep_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:22.311344+00:00
-- url     : https://prove2.me/theorems/f0c05cb0-ca54-4c07-9e98-a9c34cf38a1a
-- title:
--   Restricted Tensor: m Gen Subrep le
-- statement:
--   The Restricted Tensor construction uses the m Gen Subrep le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L233-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L233-L237

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
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
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
variable (ρ : Representation ℂ M V)

theorem GroundTheory.Automorphic.RestrictedTensor.mGenSubrep_le {N : Submodule ℂ V} {X : Subrepresentation ρ} (h : N ≤ X.toSubmodule) :
    (mGenSubrep ρ N).toSubmodule ≤ X.toSubmodule := by sorry
