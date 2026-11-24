-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mGenQuotRep_mk
-- name    : GroundTheory.Automorphic.RestrictedTensor.mGenQuotRep_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:05.301717+00:00
-- url     : https://prove2.me/theorems/9baa6c23-734d-42c8-9cf2-5228e010f509
-- title:
--   Restricted Tensor: m Gen Quot Rep mk
-- statement:
--   The Restricted Tensor construction uses the m Gen Quot Rep mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L262-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L262-L265

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

theorem GroundTheory.Automorphic.RestrictedTensor.mGenQuotRep_mk (g : M) (u : (mGenSubrep ρ N).toSubmodule) :
    mGenQuotRep ρ e N g (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ((mGenSubrep ρ N).toRepresentation g u) := by sorry
