-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_mem_span_image_iff
-- name    : GlobalTheory.GaloisDescent.mem_span_image_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:52:04.059392+00:00
-- url     : https://prove2.me/theorems/dd4a72ff-7215-4d82-8213-7773a68f3931
-- title:
--   Galois Descent: mem span image iff
-- statement:
--   The Galois Descent construction uses the mem span image iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L175-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L175-L192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L V M G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
  [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M] {f : V →ₗ[K] M}

theorem GlobalTheory.GaloisDescent.mem_span_image_iff (hf : IsBaseChange L f) (N : Submodule K V) (x : M) :
    x ∈ Submodule.span L (f '' N) ↔ ∀ l : L →ₗ[K] K, contract hf l x ∈ N := by sorry
