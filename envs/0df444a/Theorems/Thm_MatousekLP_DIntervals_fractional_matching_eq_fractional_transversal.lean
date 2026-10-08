-- Prove2me | Theorems.Thm_MatousekLP_DIntervals_fractional_matching_eq_fractional_transversal
-- name    : MatousekLP.DIntervals.fractional_matching_eq_fractional_transversal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T14:03:05.548536+00:00
-- url     : https://prove2.me/theorems/79e48327-5f6a-4cc6-8da0-27853abce6bc
-- title:
--   §8.6, p. 182 — ν(F) ≤ ν*(F) = τ*(F) ≤ τ(F) for every finite set system
-- statement:
--   Let $V$ be a finite set and $\mathcal F$ a system of nonempty subsets of $V$. Then the fractional transversal LP and the fractional matching LP of $\mathcal F$ both have optimal solutions $x^*$ and $y^*$, their optimal values agree, and they sit between the matching and transversal numbers:
--   $$
--   \nu(\mathcal F) \;\le\; \nu^*(\mathcal F) \;=\; \tau^*(\mathcal F) \;\le\; \tau(\mathcal F).
--   $$
--   Here $\tau^*(\mathcal F) = \sum_{v \in V} x^*_v$ is the minimum total weight of a fractional transversal and $\nu^*(\mathcal F) = \sum_{F \in \mathcal F} y^*_F$ the maximum total weight of a fractional matching.
--
--   The equality is the linear-programming duality between the two relaxations; it is the step in the proof of Lemma 8.6.3 that turns a bound on fractional matchings of $d$-intervals into a fractional transversal of small weight.
--
--   **Formalization Note** The statement asserts the existence of a fractional transversal $x$ and a fractional matching $y$ such that $x$ is optimal (its objective is $\le$ that of every fractional transversal), $y$ is optimal, and $\nu(\mathcal F) \le \sum_F y_F = \sum_v x_v \le \tau(\mathcal F)$; this is the book's chain with $\tau^*$, $\nu^*$ written as attained optima rather than as possibly empty infima and suprema. The book states the chain "always"; the members of $\mathcal F$ are assumed nonempty, which the book tacitly assumes as well: if $\emptyset \in \mathcal F$ there is no transversal ($\tau$ undefined), the fractional transversal LP is infeasible and the fractional matching LP is unbounded.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, §8.6, p. 182, displayed chain ν(F) ≤ ν*(F) = τ*(F) ≤ τ(F) (unnumbered)

import Mathlib
import Definitions.Def_MatousekLP_DIntervals_SetSystem

open Finset

namespace MatousekLP.DIntervals

/-- §8.6, p. 182: for a finite set system `F` on a finite set `V` whose members are nonempty,
the fractional transversal LP and the fractional matching LP both have optimal solutions `x`,
`y` with the same objective value, `ν*(F) = τ*(F)`, and
`ν(F) ≤ ν*(F) = τ*(F) ≤ τ(F)`. -/
theorem fractional_matching_eq_fractional_transversal {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Finset V)) (hF : ∀ S ∈ F, S.Nonempty) :
    ∃ (x : V → ℝ) (y : Finset V → ℝ),
      IsFractionalTransversal F x ∧ IsFractionalMatching F y ∧
      (∀ x' : V → ℝ, IsFractionalTransversal F x' → ∑ v, x v ≤ ∑ v, x' v) ∧
      (∀ y' : Finset V → ℝ, IsFractionalMatching F y' → ∑ S ∈ F, y' S ≤ ∑ S ∈ F, y S) ∧
      (matchingNumber F : ℝ) ≤ ∑ S ∈ F, y S ∧
      ∑ S ∈ F, y S = ∑ v, x v ∧
      ∑ v, x v ≤ (transversalNumber F : ℝ) := by sorry

end MatousekLP.DIntervals
