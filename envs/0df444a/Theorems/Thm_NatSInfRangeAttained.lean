-- Prove2me | Theorems.Thm_NatSInfRangeAttained
-- name    : NatSInfRangeAttained
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T20:44:28.226058+00:00
-- url     : https://prove2.me/theorems/9ad02717-4507-4a97-ab25-87e79f1c5de7
-- title:
--   Attainment of a natural-valued infimum
-- statement:
--   Let $f : \alpha\to\mathbb N$ be a natural-valued function on a nonempty type. Then the infimum of its range is attained:
--
--   $$
--   \exists a:\alpha,\quad f(a)=\inf\operatorname{range}(f),
--   \qquad
--   \forall b:\alpha,\quad \inf\operatorname{range}(f)\le f(b).
--   $$
--
--   This finite-order attainment principle supplies a drawing with minimum crossing-set cardinality when defining a graph crossing number by an infimum over all drawings.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/NatSInfRangeAttained.lean#L1-L20

import Mathlib.Order.Lattice.Nat

open Classical
noncomputable section

lemma NatSInfRangeAttained {α : Type*} (f : α → ℕ) (hα : Nonempty α) :
    ∃ a : α, f a = sInf (Set.range f) ∧
      ∀ b : α, sInf (Set.range f) ≤ f b := by sorry
