-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_adjoin_eq_top
-- name    : GroundTheory.Automorphic.RestrictedTensor.adjoin_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:35.063966+00:00
-- url     : https://prove2.me/theorems/316350ee-6afa-4baf-ae68-3dc1f2980551
-- title:
--   Restricted Tensor: adjoin eq top
-- statement:
--   The Restricted Tensor construction uses the adjoin eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L57-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L57-L92

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
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
open Module
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable [FiniteDimensional ℂ M]

theorem GroundTheory.Automorphic.RestrictedTensor.adjoin_eq_top {T : Set (End ℂ M)} (h : IsSimpleUnder T) : Algebra.adjoin ℂ T = ⊤ := by sorry
