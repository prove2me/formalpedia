-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_span_image_injective
-- name    : GlobalTheory.GaloisDescent.span_image_injective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:43.44792+00:00
-- url     : https://prove2.me/theorems/e28d243f-25a8-4730-b250-981708db59da
-- title:
--   Galois Descent: span image injective
-- statement:
--   The Galois Descent construction uses the span image injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L201-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L201-L204

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

theorem GlobalTheory.GaloisDescent.span_image_injective (hf : IsBaseChange L f) :
    Function.Injective fun N : Submodule K V => Submodule.span L (f '' N) := by sorry
