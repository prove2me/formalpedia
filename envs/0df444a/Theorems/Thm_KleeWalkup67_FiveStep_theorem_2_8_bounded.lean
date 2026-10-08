-- Prove2me | Theorems.Thm_KleeWalkup67_FiveStep_theorem_2_8_bounded
-- name    : KleeWalkup67.FiveStep.theorem_2_8_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:59:14.277368+00:00
-- url     : https://prove2.me/theorems/098caea5-c479-4227-9cdb-539166e05f1c
-- title:
--   2.8 THEOREM (bounded part, n ≥ 2d clause) — Δb(d, n) is realized on a simple polytope, at vertices on no common facet
-- statement:
--   Let $1\le d<n$, let $P\subset\mathbb R^d$ be a $d$-polytope with $n$ facets, and let $u,v$ be vertices of $P$. Then there are a **simple** $d$-polytope $P'\subset\mathbb R^d$ with $n$ facets and vertices $x,y$ of $P'$ such that
--   $$\delta_P(u,v)\le\delta_{P'}(x,y),$$
--   and, when $n\ge 2d$, $x$ and $y$ can be chosen so that they do not lie on a common facet of $P'$.
--
--   The paper states this as: "The value $\Delta_b(d,n)$, $1\le d<n$, can be realized as the distance between vertices $x$ and $y$ of a simple $d$-polytope $P$ with $n$ facets. … When $n\ge 2d$ the requirement may be added (for $\Delta$ and $\Delta_b$) that $x$ and $y$ do not lie on the same facet of $P$." Here $\Delta_b(d,n)$ is the maximum of $\delta_P(x,y)$ over all $d$-polytopes $P$ with $n$ facets and vertices $x,y$; the statement above says the same thing polytope by polytope (apply it to a pair realizing the maximum, or note that the realizing pair dominates every pair), without naming the maximum.
--
--   For $n=2d$ the conclusion says that $(P',x,y)$ is a bounded simple $d$-dimensional Dantzig figure: each of $x,y$ lies on exactly $d$ of the $2d$ facets and the two sets are disjoint. This is how §4 uses the theorem: to prove $\Delta_b(d,2d)\le d$ it suffices to bound $\delta_P(x,y)$ on bounded simple Dantzig figures.
--
--   **Formalization Note** Polytopes are facet presentations `(a, b)` with `n` rows in $\mathbb R^d$ that are bounded. "$\delta_P(u,v)\le\delta_{P'}(x,y)$" is written without a distance function: every walk of $L$ steps from $x$ to $y$ in $P'$ gives one of $L$ steps from $u$ to $v$ in $P$ (`Hirsch.Reach`, stationary steps allowed). "Do not lie on the same facet" is disjointness of the tight-row sets. Only the $\Delta_b$ sentence of 2.8 is stated; the $\Delta$ sentence (unbounded edges at $x$ and $y$) is not used by this mission. The paper's proof rests on its Lemma 2.6, a simple perturbation result whose proof the paper defers to a separate paper by Walkup.
-- source:
--   Klee & Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Math. 117 (1967), p. 60, 2.8 THEOREM (first and last sentences, Δb part); proof pp. 60–62

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra

open scoped RealInnerProductSpace

namespace KleeWalkup67.FiveStep

/-- 2.8 THEOREM, p. 60, the bounded part with the `n ≥ 2d` clause: for every `d`-polytope with
`n` facets and vertices `u, v` there is a simple `d`-polytope with `n` facets and vertices
`x, y` at least as far apart, and when `n ≥ 2d` the vertices `x, y` can be taken on no common
facet. -/
theorem theorem_2_8_bounded {d n : ℕ} (hd : 1 ≤ d) (hdn : d < n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hF : IsFacetPresentation a b) (hB : Bornology.IsBounded (Hirsch.Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b)) :
    ∃ (a' : Fin n → EuclideanSpace ℝ (Fin d)) (b' : Fin n → ℝ),
      IsFacetPresentation a' b' ∧ Bornology.IsBounded (Hirsch.Hpoly a' b') ∧ IsSimple a' b' ∧
      ∃ x ∈ Set.extremePoints ℝ (Hirsch.Hpoly a' b'),
        ∃ y ∈ Set.extremePoints ℝ (Hirsch.Hpoly a' b'),
          (∀ L : ℕ, Hirsch.Reach (Hirsch.Hpoly a' b') L x y → Hirsch.Reach (Hirsch.Hpoly a b) L u v) ∧
          (2 * d ≤ n → Disjoint (TightSet a' b' x) (TightSet a' b' y)) := by sorry

end KleeWalkup67.FiveStep
