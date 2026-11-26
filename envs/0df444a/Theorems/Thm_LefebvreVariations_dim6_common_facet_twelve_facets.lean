-- Prove2me | Theorems.Thm_LefebvreVariations_dim6_common_facet_twelve_facets
-- name    : LefebvreVariations.dim6_common_facet_twelve_facets
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:13:42.575281+00:00
-- url     : https://prove2.me/theorems/a9353921-1166-5db9-b403-bcf9200f5321
-- title:
--   Lefebvre's variations, No. 175 — on a theme by Klee and Walkup: vertices of a bounded $6$-polytope with $12$ facets on a common facet are at distance at most $6$
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $P=\{x\in\mathbb{R}^6:\ \langle a_i,x\rangle\le b_i,\ i=1,\dots,12\}$ be a bounded polyhedron such that $P$ has nonempty interior and each of the 12 inequalities is irredundant (dropping inequality $i$ lets in a point violating it). So $P$ is a $6$-polytope with exactly $12$ facets, one per inequality. Write $G(P)$ for its vertex–edge graph; $\mathrm{Reach}_k(u,v)$ means that $u,v$ are joined by a walk of exactly $k$ steps, each step being either stationary or along an edge of $P$ (equivalently $\operatorname{dist}_{G(P)}(u,v)\le k$).
--
--   Let $u,v$ be vertices of $P$ lying on a common facet. Then $\mathrm{Reach}_6(u,v)$, i.e. $u$ and $v$ are at distance at most $6$ in $G(P)$.
--
--   Mathematically it follows from the bound $\Delta_b(5,11)=6$ applied inside the common facet; the formal statement asks directly for a walk in $P$.
--
--   **Formalization Note** `Hirsch.Hpoly a b` is the set of $x$ with `⟪a i, x⟫ ≤ b i` for all `i`; `SantosHirsch.Counter.IsFacetPresentation a b` says that its interior is nonempty and that every row is irredundant; `Bornology.IsBounded` is boundedness; `Set.extremePoints ℝ` are the vertices; `Hirsch.Reach P k u v` is a walk `w 0 = u, …, w k = v` with each step stationary or `Hirsch.Adj` (the segment is an extreme subset, i.e. an edge); `SantosHirsch.Counter.IsSpindle a b u v` says that `u ≠ v` are vertices and every row is tight at exactly one of them (platform definitions).
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `HirschDim4.h12_6_bound` (every $6$-polytope with $12$ facets has combinatorial diameter at most $6$; milestone of the mission `HirschDim4.counterexample_dim4`). For $n\le 2d$ facets, two distinct vertices either share a facet or have disjoint facet sets; a vertex lies on at least $d$ facets (proved in Lean: an extreme point of an H-polyhedron has at least $d$ tight rows, otherwise one moves along a direction orthogonal to them), so with $n=2d$ disjoint facet sets cover all rows and the pair is a spindle. The verified reduction proves the base statement from this statement together with its companion `dim6_spindle_twelve_facets` (spindles). This statement is the common-facet case: a special case of the base statement (same conclusion, stronger hypothesis on the pair).
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). D. Bremner and L. Schewe, Edge-graph diameter bounds for convex polytopes with few facets, Experimental Mathematics 20 (2011), 229–237; D. Bremner, A. Deza, W. Hua and L. Schewe, More bounds on the diameters of convex polytopes, Optimization Methods and Software 28 (2013), 442–450 (computer-assisted values $\Delta_b(6,12)=6$ and $\Delta_b(4,12)=7$; citation from memory, to be checked before publication) (the facet is a $5$-polytope with at most $11$ facets, $\Delta_b(5,11)=6$; citation from memory). Origin of this statement: it is the missing step (together with `dim6_spindle_twelve_facets`) of a reduction of HirschDim4.h12_6_bound, a milestone of the mission HirschDim4.counterexample_dim4.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_SantosHirsch_Counter_Setting

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace LefebvreVariations

theorem dim6_common_facet_twelve_facets (a : Fin 12 → EuclideanSpace ℝ (Fin 6)) (b : Fin 12 → ℝ)
    (u v : EuclideanSpace ℝ (Fin 6))
    (hfp : SantosHirsch.Counter.IsFacetPresentation a b)
    (hbd : Bornology.IsBounded (Hirsch.Hpoly a b))
    (hu : u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hcomm : ∃ i, ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i) :
    Hirsch.Reach (Hirsch.Hpoly a b) 6 u v := by
  sorry

end LefebvreVariations
