-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isSimpleUnder_winOps
-- name    : GroundTheory.Automorphic.RestrictedTensor.isSimpleUnder_winOps
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:19.407942+00:00
-- url     : https://prove2.me/theorems/6bed075a-0928-4db1-ac6a-b6e946a55da3
-- title:
--   Restricted Tensor: is Simple Under win Ops
-- statement:
--   The Restricted Tensor construction uses the is Simple Under win Ops property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L158-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L158-L176

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

theorem GroundTheory.Automorphic.RestrictedTensor.isSimpleUnder_winOps [ρ.IsIrreducible] (he : IsWinProj ρ e)
    (hne : LinearMap.range e ≠ ⊥) : IsSimpleUnder (winOps ρ e) := by sorry
