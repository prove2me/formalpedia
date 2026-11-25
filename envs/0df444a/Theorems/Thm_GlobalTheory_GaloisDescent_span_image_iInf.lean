-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_span_image_iInf
-- name    : GlobalTheory.GaloisDescent.span_image_iInf
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:52.834097+00:00
-- url     : https://prove2.me/theorems/94882cbc-c3cf-40dd-ad48-41d6bf60b698
-- title:
--   Galois Descent: span image i Inf
-- statement:
--   The Galois Descent construction uses the span image i Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L206-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L206-L210

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

theorem GlobalTheory.GaloisDescent.span_image_iInf (hf : IsBaseChange L f) {J : Sort*} (N : J → Submodule K V) :
    Submodule.span L (f '' (⨅ j, N j : Submodule K V)) = ⨅ j, Submodule.span L (f '' N j) := by sorry
