-- Prove2me | Theorems.Thm_KleeWalkup67_FiveStep_lemma_2_7
-- name    : KleeWalkup67.FiveStep.lemma_2_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T05:49:19.350663+00:00
-- url     : https://prove2.me/theorems/d1adebdd-cb5d-4f4d-8080-d61a82b84ba8
-- title:
--   Lemma 2.7 — facial-path transfer in all three boundedness regimes
-- statement:
--   Let $d,n,r$ and $k_1,\ldots,k_r$ be positive integers with $k_i\le d$. Fix any one of the three regimes: bounded, unbounded, or unrestricted. If every simple triple $(P,x,y)$ of class $(d,n)$ in that regime admits a $(k_1,\ldots,k_r)$-facial path from $x$ to $y$, then every triple of that class in the same regime admits such a path.
--
--   A facial path consists of nonempty faces of the specified dimensions; the first contains $x$, the last contains $y$, and consecutive faces have nonempty intersection. It need not be an ordinary edge path. This transfers uniform facial-path existence from simple to arbitrary pointed polyhedra.
--
--   Differences from the source:
--   - encoding: d-dimensional polyhedra in finite-dimensional real vector spaces with n geometric facets → irredundant real facet presentations in EuclideanSpace ℝ (Fin d) with n rows; reason: choose affine coordinates in the affine hull; nonempty interior and irredundancy preserve exactly the source instances
--   - encoding: pointed simple polyhedra have exactly d edges at each vertex → the published IsSimple counts exactly d incident facets at each vertex; reason: these characterizations are equivalent for pointed d-polyhedra with geometric facet presentations
--   - encoding: r positive integers k₁,…,kᵣ, with r positive → a nonempty list ks of positive natural numbers, each at most d; reason: the list length is r and every finite positive sequence is represented
--   - encoding: three assertions, for bounded, unbounded, and unrestricted triples → one assertion universally quantified over Option Bool, decoded by InRegime; reason: some true, some false, and none enumerate exactly these three regimes
-- source:
--   Klee and Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Mathematica 117 (1967), 53–78, https://doi.org/10.1007/BF02395040, p.60 (PDF8), Lemma 2.7.

import Definitions.Def_KleeWalkup67_Support_Classes

namespace KleeWalkup67.FiveStep

theorem lemma_2_7 (d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (ks : List ℕ) (hks : ks ≠ []) (hk : ∀ k ∈ ks, 0 < k ∧ k ≤ d)
    (regime : Option Bool)
    (hSimple : ∀ (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Support.IsClass a b → IsSimple a b →
      Support.InRegime regime (Hirsch.Hpoly a b) →
      ∀ x ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ y ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b), IsFacialPath a b ks x y) :
    ∀ (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Support.IsClass a b → Support.InRegime regime (Hirsch.Hpoly a b) →
      ∀ x ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ y ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b), IsFacialPath a b ks x y := by sorry

end KleeWalkup67.FiveStep
