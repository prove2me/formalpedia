-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_IsStable_mono
-- name    : GroundTheory.Automorphic.RestrictedTensor.IsStable.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:25.336813+00:00
-- url     : https://prove2.me/theorems/5d8c1eab-2eca-49de-b90b-228fd7bb3933
-- title:
--   Is Stable: mono
-- statement:
--   The Is Stable construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Operators.lean#L51-L53

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

theorem GroundTheory.Automorphic.RestrictedTensor.IsStable.mono {T₁ T₂ : Set (End ℂ M)} {p : Submodule ℂ M} (h : IsStable T₂ p)
    (hT : T₁ ⊆ T₂) : IsStable T₁ p := by sorry
