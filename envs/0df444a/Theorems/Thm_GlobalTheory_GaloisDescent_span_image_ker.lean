-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_span_image_ker
-- name    : GlobalTheory.GaloisDescent.span_image_ker
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:43.376287+00:00
-- url     : https://prove2.me/theorems/8cf33291-5892-4593-b66d-40b17063ea37
-- title:
--   Galois Descent: span image ker
-- statement:
--   The Galois Descent construction uses the span image ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L234-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L234-L238

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
variable {V' M' : Type*} [AddCommGroup V'] [Module K V']
  [AddCommGroup M'] [Module K M'] [Module L M'] [IsScalarTower K L M'] {f' : V' →ₗ[K] M'}

theorem GlobalTheory.GaloisDescent.span_image_ker (hf : IsBaseChange L f) (hf' : IsBaseChange L f') (p : V →ₗ[K] V')
    (F : M →ₗ[L] M') (hF : ∀ v, F (f v) = f' (p v)) :
    Submodule.span L (f '' LinearMap.ker p) = LinearMap.ker F := by sorry
