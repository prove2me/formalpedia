-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_separable_point_of_separableClosure_point
-- name    : GlobalTheory.exists_finite_separable_point_of_separableClosure_point
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:32:52.15983+00:00
-- url     : https://prove2.me/theorems/c3d85784-38ea-460b-bde2-70607967de1f
-- title:
--   Global Theory: exists finite separable point of separable Closure point
-- statement:
--   The Global Theory construction uses the exists finite separable point of separable Closure point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteSeparablePointOfSeparableClosurePoin.lean#L6-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteSeparablePointOfSeparableClosurePoin.lean#L6-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteSeparablePointOfSeparableClosurePoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_finite_separable_point_of_separableClosure_point :
    ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B], Algebra.FiniteType k B →
      Nonempty (B →ₐ[k] SeparableClosure k) →
      ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'),
        FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by sorry
