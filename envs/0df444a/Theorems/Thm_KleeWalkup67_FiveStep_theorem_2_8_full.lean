-- Prove2me | Theorems.Thm_KleeWalkup67_FiveStep_theorem_2_8_full
-- name    : KleeWalkup67.FiveStep.theorem_2_8_full
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T05:49:27.714027+00:00
-- url     : https://prove2.me/theorems/1373aade-16b1-4c5f-b635-1391f90496de
-- title:
--   Theorem 2.8 — full extremal realization, including unbounded endpoint edges
-- statement:
--   Write $\Delta_b(d,n)$ for the maximum vertex-edge distance among bounded triples of class $(d,n)$, and $\Delta(d,n)$ for the maximum among all triples of that class.
--
--   1. For every $1\le d<n$, there exist a simple $d$-polytope $P$ with exactly $n$ facets and vertices $x,y$ such that $\delta_P(x,y)=\Delta_b(d,n)$.
--   2. For every $2\le d<n$, there exist a simple $d$-polyhedron $P$ with exactly $n$ facets and vertices $x,y$ such that $\delta_P(x,y)=\Delta(d,n)$, with both vertices incident to unbounded edges of $P$.
--   3. In each assertion, when $n\ge2d$, the realizing vertices can simultaneously be chosen to share no facet.
--
--   Realization means that an integer $L$ is the actual distance between the chosen vertices and bounds the distance of every vertex pair in every eligible polyhedron. The chosen polyhedron is existentially asserted before all competing triples; no input polyhedron or nonemptiness of the class is assumed.
--
--   The first assertion is retained exactly at the printed parameter range. It therefore includes the false case $d=1,n=3$: a bounded one-dimensional polyhedron has two facets, never three. This source defect is recorded in insight I1, and is not repaired in this item. The bounded five-step goal is a separate existing target.
--
--   Differences from the source:
--   - encoding: d-dimensional polyhedra in finite-dimensional real vector spaces with n geometric facets → irredundant real facet presentations in EuclideanSpace ℝ (Fin d) with n rows; reason: choose affine coordinates in the affine hull; nonempty interior and irredundancy preserve exactly the source instances
--   - encoding: pointed simple polyhedra have exactly d edges at each vertex → the published IsSimple counts exactly d incident facets at each vertex; reason: these characterizations are equivalent for pointed d-polyhedra with geometric facet presentations
--   - encoding: the maximum Δ or Δ_b is realized as a vertex distance → there exist a polyhedron, two vertices, and L with Reach L, no Reach k for k<L, and a universal DiamLE L bound on the appropriate class; reason: this states attainment and maximality together and preserves the existence assertion even for empty parameter classes
--   - encoding: ordinary edge paths of length at most L → Hirsch.Reach and Hirsch.DiamLE use L steps allowing stationary steps; reason: delete stationary steps or pad with them; vertex endpoints give exactly the same distance
--   - encoding: neither endpoint lies on a common facet when n≥2d → the endpoint tight-row sets are disjoint under the same inequality; reason: irredundant rows are in bijection with geometric facets
--   - encoding: both vertices are incident to unbounded edges → each belongs to a nonempty face of affine dimension one that is not Bornology.IsBounded; reason: these are the geometric unbounded one-faces in the source
-- source:
--   Klee and Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Mathematica 117 (1967), 53–78, https://doi.org/10.1007/BF02395040, p.60 (PDF8), Theorem 2.8.

import Definitions.Def_KleeWalkup67_Support_Classes

namespace KleeWalkup67.FiveStep

theorem theorem_2_8_full :
    (∀ d n : ℕ, 1 ≤ d → d < n →
      ∃ (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
        Support.IsClass a b ∧ IsSimple a b ∧ Bornology.IsBounded (Hirsch.Hpoly a b) ∧
        ∃ x ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
        ∃ y ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
          (2 * d ≤ n → Disjoint (TightSet a b x) (TightSet a b y)) ∧
          ∃ L : ℕ, Hirsch.Reach (Hirsch.Hpoly a b) L x y ∧
            (∀ k < L, ¬ Hirsch.Reach (Hirsch.Hpoly a b) k x y) ∧
            (∀ (c : Fin n → EuclideanSpace ℝ (Fin d)) (e : Fin n → ℝ),
              Support.IsClass c e → Bornology.IsBounded (Hirsch.Hpoly c e) →
              Hirsch.DiamLE (Hirsch.Hpoly c e) L)) ∧
    (∀ d n : ℕ, 2 ≤ d → d < n →
      ∃ (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
        Support.IsClass a b ∧ IsSimple a b ∧
        ∃ x ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
        ∃ y ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
          Support.IncidentUnboundedEdge a b x ∧ Support.IncidentUnboundedEdge a b y ∧
          (2 * d ≤ n → Disjoint (TightSet a b x) (TightSet a b y)) ∧
          ∃ L : ℕ, Hirsch.Reach (Hirsch.Hpoly a b) L x y ∧
            (∀ k < L, ¬ Hirsch.Reach (Hirsch.Hpoly a b) k x y) ∧
            (∀ (c : Fin n → EuclideanSpace ℝ (Fin d)) (e : Fin n → ℝ),
              Support.IsClass c e → Hirsch.DiamLE (Hirsch.Hpoly c e) L)) := by sorry

end KleeWalkup67.FiveStep
