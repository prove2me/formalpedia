-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_with_nonnegative_first_fare
-- name    : NestedSeatAlloc.IntPolicy.theorem1_with_nonnegative_first_fare
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:41:31.823365+00:00
-- url     : https://prove2.me/theorems/203bc287-d135-4984-ac6d-136a52d3f56b
-- title:
--   Theorem 1 conditional concavity and optimality with nonnegative first fare
-- statement:
--   This theorem has exactly the conclusion of the published
--   general Theorem 1, under one extra explicit premise f(1)>=0.
--   The first-class concavity lemma
--   expRevenue_one_concave_nonneg_fare gives the base of the
--   expected-revenue concavity induction. The separately Proved
--   theorem1_of_first_class_concavity supplies the entire stated
--   conclusion, conditional concavity at every higher level and
--   global optimality, from condition (20) and base concavity.
--
--   The original IsSeatModel type does not itself require positive
--   fares. Therefore the theorem explicitly retains hf1 until
--   someone proves that it follows from SubdiffCondition, or finds
--   another valid base argument. The original published full
--   Theorem 1 remains Open until that happens.
--   Only remote Prove2Me compilation is authoritative.
-- source:
--   This theorem has exactly the conclusion of the published
--   general Theorem 1, under one extra explicit premise f(1)>=0.
--   The first-class concavity lemma
--   expRevenue_one_concave_nonneg_fare gives the base of the
--   expected-revenue concavity induction. The separately Proved
--   theorem1_of_first_class_concavity supplies the entire stated
--   conclusion, conditional concavity at every higher level and
--   global optimality, from condition (20) and base concavity.
--
--   The original IsSeatModel type does not itself require positive
--   fares. Therefore the theorem explicitly retains hf1 until
--   someone proves that it follows from SubdiffCondition, or finds
--   another valid base argument. The original published full
--   Theorem 1 remains Open until that happens.
--   Only remote Prove2Me compilation is authoritative.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.theorem1_with_nonnegative_first_fare {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h20 : SubdiffCondition P X f p)
    (hf1 : 0 ≤ f 1) :
    (∀ k, 1 ≤ k → ∀ y, 0 ≤ y →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y)) ∧
      IsOptimal P X f p := by sorry
