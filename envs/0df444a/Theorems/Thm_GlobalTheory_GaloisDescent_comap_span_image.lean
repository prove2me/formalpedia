-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_comap_span_image
-- name    : GlobalTheory.GaloisDescent.comap_span_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:52:25.769802+00:00
-- url     : https://prove2.me/theorems/d7e47a09-987c-479b-bca3-a7e7b4a0edb9
-- title:
--   Galois Descent: comap span image
-- statement:
--   The Galois Descent construction uses the comap span image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L194-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L194-L199

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

theorem GlobalTheory.GaloisDescent.comap_span_image (hf : IsBaseChange L f) (N : Submodule K V) :
    ((Submodule.span L (f '' N)).restrictScalars K).comap f = N := by sorry
