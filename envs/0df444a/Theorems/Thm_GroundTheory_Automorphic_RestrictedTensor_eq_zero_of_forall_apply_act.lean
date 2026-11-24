-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eq_zero_of_forall_apply_act
-- name    : GroundTheory.Automorphic.RestrictedTensor.eq_zero_of_forall_apply_act
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:33:02.228055+00:00
-- url     : https://prove2.me/theorems/df07f883-3543-4f65-8ca9-4d708d660d1b
-- title:
--   Restricted Tensor: eq zero of forall apply act
-- statement:
--   The Restricted Tensor construction uses the eq zero of forall apply act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/MatrixCoeff.lean#L57-L60

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
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
open Set
open GroundTheory.Automorphic.RestrictedTensor
variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

theorem GroundTheory.Automorphic.RestrictedTensor.eq_zero_of_forall_apply_act {ρ : Representation ℂ G V} [ρ.IsIrreducible]
    {l : Module.Dual ℂ V} (hl : l ≠ 0) {x : V} (h : ∀ g, l (ρ g x) = 0) : x = 0 := by sorry
