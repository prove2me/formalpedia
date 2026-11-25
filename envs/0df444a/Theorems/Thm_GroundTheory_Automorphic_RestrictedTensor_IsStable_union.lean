-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_IsStable_union
-- name    : GroundTheory.Automorphic.RestrictedTensor.IsStable.union
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:10.1322+00:00
-- url     : https://prove2.me/theorems/f91eb22f-d7fe-4b14-a182-16d3d275165f
-- title:
--   Is Stable: union
-- statement:
--   The Is Stable construction uses the union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L46-L49

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

theorem GroundTheory.Automorphic.RestrictedTensor.IsStable.union {T₁ T₂ : Set (End ℂ M)} {p : Submodule ℂ M} (h₁ : IsStable T₁ p)
    (h₂ : IsStable T₂ p) : IsStable (T₁ ∪ T₂) p := by sorry
