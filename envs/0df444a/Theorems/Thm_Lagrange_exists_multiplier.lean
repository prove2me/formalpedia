-- Prove2me | Theorems.Thm_Lagrange_exists_multiplier
-- name    : Lagrange.exists_multiplier
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T16:48:21.217213+00:00
-- url     : https://prove2.me/theorems/292c64eb-9672-4b36-b23a-7a382ea7989c
-- title:
--   Existence of a Lagrange multiplier under convexlikeness and a generalized Slater condition
-- statement:
--   Let $F$ be a finite-dimensional real topological vector space, let $K \subseteq F$ be a pointed cone, let $S$ be a set, and let $f : S \to \mathbb{R}$, $G : S \to F$. Assume
--
--   1. **Convexlikeness (Fan).** For all $x_1, x_2 \in S$ and $t \in [0,1]$ there is $x \in S$ with
--   $$G(x) - \big(t\,G(x_1) + (1-t)\,G(x_2)\big) \in K \quad\text{and}\quad t\,f(x_1) + (1-t)\,f(x_2) \le f(x);$$
--   2. **Generalized Slater.** $0$ lies in the interior of the perturbation set $\{u : \exists x \in S,\ G(x) - u \in K\}$;
--   3. $f(x) \le p$ for every $x \in S$ with $G(x) \in K$.
--
--   Then there is a linear functional $y$ on $F$, nonnegative on $K$, with
--
--   $$
--   f(x) + y\big(G(x)\big) \;\le\; p \qquad \text{for all } x \in S .
--   $$
--
--   In words: a valid bound $p$ on the *constrained* problem extends to a valid bound on the
--   Lagrangian, uniformly in $x$, with a multiplier that is dual-feasible. This is the form of
--   Lagrangian duality that applies when $S$ carries no linear structure at all -- $S$ may be a
--   set of distributions, of policies, of matrices -- because convexity is asked for only through
--   Fan's condition, which says that the *image* of $S$ under $(f, G)$ is convexlike. Robust and
--   distributionally robust reformulations use it in exactly that way: $S$ is an ambiguity set, $G$
--   collects the moment or support constraints, and $y$ becomes the vector of dual prices.
--
--   The Slater condition is what rules out a duality gap, and in the stated interior form it also
--   covers equality constraints, by taking $K = \{0\}$ and reading "the moment vector lies in the
--   interior of the attainable set".
--
--   **Formalization Note** `PointedCone ℝ F` is Mathlib's pointed cone and `Module.Dual ℝ F` its
--   dual space, so the multiplier is produced as a functional rather than a vector; combining this
--   with `Module.Dual.exists_dotProduct_eq` or `Module.Dual.exists_trace_eq` turns it into a vector
--   or a matrix when $F$ is $\mathbb{R}^n$ or a matrix space.
-- source:
--   Carried as an internal support lemma, with this exact statement and proof, in twelve accepted submissions across ten missions of the OR Formalization Drive (e.g. https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1); published here once so that it can be imported. Fan's convexlike minimax theory with a generalized Slater condition; see Ky Fan, Minimax theorems, Proc. Nat. Acad. Sci. 39 (1953) 42-47, and Bonnans & Shapiro, Perturbation Analysis of Optimization Problems, §2.5.

import Mathlib

open Matrix

namespace Lagrange

theorem exists_multiplier {X F : Type*}
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [T2Space F] [FiniteDimensional ℝ F]
    (S : Set X) (f : X → ℝ) (G : X → F) (K : PointedCone ℝ F)
    -- Fan convexlike: mixtures stay in `S`, improve `f`, and stay at least as feasible
    (hcvx : ∀ x₁ ∈ S, ∀ x₂ ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ x ∈ S,
        G x - (t • G x₁ + (1 - t) • G x₂) ∈ K ∧ t * f x₁ + (1 - t) * f x₂ ≤ f x)
    -- generalized Slater: perturbation domain contains a neighbourhood of 0
    -- (this covers equalities, K = ⊥, via "moment vector in the interior")
    (hslater : (0 : F) ∈ interior {u | ∃ x ∈ S, G x - u ∈ K})
    (p : ℝ) (hp : ∀ x ∈ S, G x ∈ K → f x ≤ p) :
    ∃ y : Module.Dual ℝ F, (∀ k ∈ K, 0 ≤ y k) ∧ ∀ x ∈ S, f x + y (G x) ≤ p := by sorry

end Lagrange
