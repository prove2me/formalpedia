-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mGenQuotMk_injective
-- name    : GroundTheory.Automorphic.RestrictedTensor.mGenQuotMk_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:29.882068+00:00
-- url     : https://prove2.me/theorems/73795b01-61a6-4eed-a481-6a30e77abcf9
-- title:
--   Restricted Tensor: m Gen Quot Mk injective
-- statement:
--   The Restricted Tensor construction uses the m Gen Quot Mk injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L269-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L269-L279

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

theorem GroundTheory.Automorphic.RestrictedTensor.mGenQuotMk_injective (he : IsWinProj ρ e) (hNe : N ≤ LinearMap.range e) :
    Function.Injective (mGenQuotMk ρ e N) := by sorry
