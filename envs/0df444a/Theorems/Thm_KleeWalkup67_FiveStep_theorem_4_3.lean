-- Prove2me | Theorems.Thm_KleeWalkup67_FiveStep_theorem_4_3
-- name    : KleeWalkup67.FiveStep.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:07:38.425902+00:00
-- url     : https://prove2.me/theorems/4f4c3c77-aeae-467f-bb3b-73fdfcd11f74
-- title:
--   4.3 THEOREM — Δb(5, 10) = 5: every 5-polytope with 10 facets has diameter at most 5, and 5 is attained
-- statement:
--   $\Delta_b(d,n)$ is the maximum diameter of $d$-dimensional polytopes with $n$ facets, the diameter being the least $l$ such that any two vertices are joined by a path of at most $l$ edges. The theorem asserts
--   $$\Delta_b(5,10)=5,$$
--   in two halves:
--
--   1. every $5$-dimensional polytope $P\subset\mathbb R^5$ with $10$ facets has diameter at most $5$: any two vertices are joined by a path of at most $5$ edges;
--   2. some $5$-dimensional polytope with $10$ facets has two vertices that are not joined by any path of at most $4$ edges.
--
--   Half 1 is the **bounded 5-step conjecture**, the case $d=5$ of $\Delta_b(d,2d)\le d$, and with the paper's reductions it gives the bounded Hirsch bound $\Delta_b(d,n)\le n-d$ whenever $n\le d+5$. Half 2 is the reverse inequality, which the paper calls "presumably well-known" and establishes incidentally in §2; the $5$-cube $[0,1]^5$ with the vertices $0$ and $(1,\dots,1)$ is a witness.
--
--   **Formalization Note** "$5$-polytope with $10$ facets" is a bounded facet presentation with $10$ rows in $\mathbb R^5$ (nonempty interior, no redundant row). $\Delta_b(5,10)=5$ is stated as an upper bound for every such polytope plus a witness, not as a supremum. A path of at most $L$ edges is `Hirsch.Reach P L` (walks of exactly $L$ steps that may stand still).
-- source:
--   Klee & Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Math. 117 (1967), p. 72, 4.3 THEOREM; Δb defined on p. 53 and p. 57; lower bound p. 54

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra

open scoped RealInnerProductSpace

namespace KleeWalkup67.FiveStep

/-- 4.3 THEOREM, p. 72: `Δb(5, 10) = 5`. Every 5-polytope with 10 facets has diameter at most 5,
and some 5-polytope with 10 facets has two vertices at distance more than 4. -/
theorem theorem_4_3 :
    (∀ (a : Fin 10 → EuclideanSpace ℝ (Fin 5)) (b : Fin 10 → ℝ),
        IsFacetPresentation a b → Bornology.IsBounded (Hirsch.Hpoly a b) →
        Hirsch.DiamLE (Hirsch.Hpoly a b) 5) ∧
    (∃ (a : Fin 10 → EuclideanSpace ℝ (Fin 5)) (b : Fin 10 → ℝ),
        IsFacetPresentation a b ∧ Bornology.IsBounded (Hirsch.Hpoly a b) ∧
        ∃ x ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
          ∃ y ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
            ¬ Hirsch.Reach (Hirsch.Hpoly a b) 4 x y) := by sorry

end KleeWalkup67.FiveStep
