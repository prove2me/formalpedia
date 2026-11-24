-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_span_image_comap_eq
-- name    : GlobalTheory.GaloisDescent.span_image_comap_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:25.554796+00:00
-- url     : https://prove2.me/theorems/3e50f8b0-f64e-44ac-97b5-a6bba436093a
-- title:
--   Galois Descent: span image comap eq
-- statement:
--   The Galois Descent construction uses the span image comap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L115-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L115-L128

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

theorem GlobalTheory.GaloisDescent.span_image_comap_eq (hf : IsBaseChange L f) (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (φ : G → M →+ M) (hφ : ∀ g a v, φ g (a • f v) = s g a • f v)
    (W : Submodule L M) (hW : ∀ g, ∀ w ∈ W, φ g w ∈ W) :
    Submodule.span L (f '' (W.restrictScalars K).comap f) = W := by sorry
