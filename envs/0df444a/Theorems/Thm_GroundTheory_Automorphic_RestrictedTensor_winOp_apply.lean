-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_winOp_apply
-- name    : GroundTheory.Automorphic.RestrictedTensor.winOp_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:44.791137+00:00
-- url     : https://prove2.me/theorems/fffb788e-a831-4a36-83c1-7c3300bc5029
-- title:
--   Restricted Tensor: win Op apply
-- statement:
--   The Restricted Tensor construction uses the win Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L155-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L155-L156

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
variable {ρ} {e : End ℂ V}

theorem GroundTheory.Automorphic.RestrictedTensor.winOp_apply (m : M) (x : LinearMap.range e) : (winOp ρ e m x : V) = e (ρ m x) := by sorry
