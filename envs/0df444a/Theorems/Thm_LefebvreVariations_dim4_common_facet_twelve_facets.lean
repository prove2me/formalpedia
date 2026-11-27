-- Prove2me | Theorems.Thm_LefebvreVariations_dim4_common_facet_twelve_facets
-- name    : LefebvreVariations.dim4_common_facet_twelve_facets
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:11:07.547217+00:00
-- url     : https://prove2.me/theorems/4431f384-bf14-4131-81d8-9f69d497957b
-- title:
--   Lefebvre's variations, No. 241 — on a theme by Klee and Walkup: vertices of a bounded $4$-polytope with $12$ facets on a common facet are at distance at most $7$
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $P=\{x\in\mathbb{R}^4:\ \langle a_i,x\rangle\le b_i,\ i=1,\dots,12\}$ be a bounded polyhedron such that $P$ has nonempty interior and each of the 12 inequalities is irredundant (dropping inequality $i$ lets in a point violating it). So $P$ is a $4$-polytope with exactly $12$ facets, one per inequality. Write $G(P)$ for its vertex–edge graph; $\mathrm{Reach}_k(u,v)$ means that $u,v$ are joined by a walk of exactly $k$ steps, each step being either stationary or along an edge of $P$ (equivalently $\operatorname{dist}_{G(P)}(u,v)\le k$).
--
--   Let $u,v$ be vertices of $P$ that lie on a common facet. Then $\mathrm{Reach}_7(u,v)$, i.e. $u$ and $v$ are at distance at most $7$ in $G(P)$.
--
--   Pairs on a common facet are the case that reduces to dimension $3$: both vertices lie in a facet, which is a $3$-polytope with at most $11$ facets whose edge graph is a subgraph of $G(P)$.
--
--   **Formalization Note** `Hirsch.Hpoly a b` is the set of $x$ with `⟪a i, x⟫ ≤ b i` for all `i`; `SantosHirsch.Counter.IsFacetPresentation a b` says that its interior is nonempty and that every row is irredundant; `Bornology.IsBounded` is boundedness; `Set.extremePoints ℝ` are the vertices; `Hirsch.Reach P k u v` is a walk `w 0 = u, …, w k = v` with each step stationary or `Hirsch.Adj` (the segment is an extreme subset, i.e. an edge); `SantosHirsch.Counter.IsSpindle a b u v` says that `u ≠ v` are vertices and every row is tight at exactly one of them (platform definitions).
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `HirschDim4.h12_4_bound` (every $4$-polytope with $12$ facets has combinatorial diameter at most $7$; milestone of the mission `HirschDim4.counterexample_dim4`). Two vertices of $P$ either lie on a common facet or on no common facet. The reduction, checked in Lean, proves the base statement from this statement and the companion statement for pairs on no common facet (`dim4_disjoint_facets_twelve_facets`). This statement is the easy half on paper: both vertices lie in a facet, a $3$-polytope with at most $11$ facets, whose diameter is at most $7$ by the Hirsch bound in dimension $3$ (which is below $8$). It is a special case of the base statement, and the formalization of the restriction to a facet is the missing step.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). D. Bremner and L. Schewe, Edge-graph diameter bounds for convex polytopes with few facets, Experimental Mathematics 20 (2011), 229–237; D. Bremner, A. Deza, W. Hua and L. Schewe, More bounds on the diameters of convex polytopes, Optimization Methods and Software 28 (2013), 442–450 (computer-assisted values $\Delta_b(6,12)=6$ and $\Delta_b(4,12)=7$; citation from memory, to be checked before publication). Origin of this statement: it is the common-facet case in a reduction of HirschDim4.h12_4_bound, a milestone of the mission HirschDim4.counterexample_dim4.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_SantosHirsch_Counter_Setting

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace LefebvreVariations

theorem dim4_common_facet_twelve_facets (a : Fin 12 → EuclideanSpace ℝ (Fin 4)) (b : Fin 12 → ℝ)
    (u v : EuclideanSpace ℝ (Fin 4))
    (hfp : SantosHirsch.Counter.IsFacetPresentation a b)
    (hbd : Bornology.IsBounded (Hirsch.Hpoly a b))
    (hu : u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hcomm : ∃ i, ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i) :
    Hirsch.Reach (Hirsch.Hpoly a b) 7 u v := by
  sorry

end LefebvreVariations
