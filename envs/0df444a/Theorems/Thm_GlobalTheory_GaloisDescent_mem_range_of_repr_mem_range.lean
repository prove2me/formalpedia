-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_mem_range_of_repr_mem_range
-- name    : GlobalTheory.GaloisDescent.mem_range_of_repr_mem_range
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:48:27.941213+00:00
-- url     : https://prove2.me/theorems/58e6831a-ca5e-4de1-9271-841e80ecd3fe
-- title:
--   Galois Descent: mem range of repr mem range
-- statement:
--   The Galois Descent construction uses the mem range of repr mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L106-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L106-L113

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

theorem GlobalTheory.GaloisDescent.mem_range_of_repr_mem_range (hf : IsBaseChange L f) {ι : Type*} (b : Basis ι K V) (u : M)
    (hu : ∀ i, (hf.basis b).repr u i ∈ Set.range (algebraMap K L)) : u ∈ LinearMap.range f := by sorry
