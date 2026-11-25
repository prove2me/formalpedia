-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_linearForm_mOrbitMap
-- name    : GroundTheory.Automorphic.RestrictedTensor.linearForm_mOrbitMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:33:09.367503+00:00
-- url     : https://prove2.me/theorems/54f8dda4-0d4e-47b5-999c-8459d97ce8e1
-- title:
--   Restricted Tensor: linear Form m Orbit Map
-- statement:
--   The Restricted Tensor construction uses the linear Form m Orbit Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L70-L74

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

theorem GroundTheory.Automorphic.RestrictedTensor.linearForm_mOrbitMap (ρ : Representation ℂ M V) (v : V) (l : Dual ℂ V) (h : M)
    (c : M →₀ ℂ) : l (ρ h (mOrbitMap ρ v c)) = c.sum fun g a => a * l (ρ (h * g) v) := by sorry
