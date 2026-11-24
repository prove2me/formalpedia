-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_evalForm_tprod
-- name    : GroundTheory.Automorphic.RestrictedTensor.evalForm_tprod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:38.452068+00:00
-- url     : https://prove2.me/theorems/c0252317-31f3-4cf0-8fbe-d3eddf04397c
-- title:
--   Restricted Tensor: eval Form tprod
-- statement:
--   The Restricted Tensor construction uses the eval Form tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L215-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L215-L220

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
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
open PiTensorProduct Filter Function Module Set
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem GroundTheory.Automorphic.RestrictedTensor.evalForm_tprod {ξ : ∀ v, V v} {l : ∀ v, Dual ℂ (V v)}
    {hl : ∀ᶠ v in cofinite, l v (ξ v) = 1} {x : ∀ v, V v} (hx : IsRestricted ξ x) :
    evalForm ξ l hl (tprod ℂ x) = ∏ᶠ v, l v (x v) := by sorry
