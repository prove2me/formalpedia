-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mGenQuotForm_apply
-- name    : GroundTheory.Automorphic.RestrictedTensor.mGenQuotForm_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:33:21.798025+00:00
-- url     : https://prove2.me/theorems/3babda4e-b630-4e43-8ccb-4e942c991778
-- title:
--   Restricted Tensor: m Gen Quot Form apply
-- statement:
--   The Restricted Tensor construction uses the m Gen Quot Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L361-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L361-L363

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
variable (e : End ℂ V) (N : Submodule ℂ V)
variable {ρ e N}

theorem GroundTheory.Automorphic.RestrictedTensor.mGenQuotForm_apply (l : Dual ℂ V) (g : M) (n : N) :
    mGenQuotForm ρ e N l (mGenQuotRep ρ e N g (mGenQuotMk ρ e N n)) = l (e (ρ g n)) := by sorry
