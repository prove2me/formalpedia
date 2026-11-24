-- Prove2me | Theorems.Thm_GlobalTheory_range_comap_includeRight_field
-- name    : GlobalTheory.range_comap_includeRight_field
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:14:56.354235+00:00
-- url     : https://prove2.me/theorems/453152b8-f0d7-44d9-938e-ff8cb549efcb
-- title:
--   Global Theory: range comap include Right field
-- statement:
--   The Global Theory construction uses the range comap include Right field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RangeComapIncludeRightField.lean#L8-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RangeComapIncludeRightField.lean#L8-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RangeComapIncludeRightField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory

theorem GlobalTheory.range_comap_includeRight_field :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : Type) [Field k] [Algebra A k],
    Set.range (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom) = {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A k)} := by sorry
