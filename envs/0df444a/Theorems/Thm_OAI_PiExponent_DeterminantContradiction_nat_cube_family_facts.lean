-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nat_cube_family_facts
-- name    : OAI.PiExponent.DeterminantContradiction.nat_cube_family_facts
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:13:04.818895+00:00
-- url     : https://prove2.me/theorems/4f7e23fc-d8b9-43da-808c-25172fc7ddc1
-- title:
--   Geometric facts about natural lattice cubes
-- statement:
--   Each natural lattice cube is measurable and has unit volume; cubes with distinct natural vector indices are disjoint. This also covers empty index sets and dimension zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.nat_cube_family_facts
    {m : ℕ} (S : Finset (Fin m → ℕ)) :
    (∀ a ∈ S, MeasurableSet
      {x : Fin m → ℝ | ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1}) ∧
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      Disjoint
        {x : Fin m → ℝ | ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1}
        {x : Fin m → ℝ | ∀ i, (b i : ℝ) ≤ x i ∧ x i < (b i : ℝ) + 1}) ∧
    (∀ a ∈ S, MeasureTheory.volume
      {x : Fin m → ℝ | ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1} = 1) := by sorry
