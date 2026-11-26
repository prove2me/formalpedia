-- Prove2me | Theorems.Thm_LefebvreVariations_dim4_common_facet_eight_facets
-- name    : LefebvreVariations.dim4_common_facet_eight_facets
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:12:26.0409+00:00
-- url     : https://prove2.me/theorems/825bfe76-4872-5566-91d9-8056f37a9826
-- title:
--   Lefebvre's variations, No. 169 — on a theme by Klee and Walkup: vertices of a bounded $4$-polytope with $8$ facets on a common facet are at distance at most $4$
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $P=\{x\in\mathbb{R}^4:\ \langle a_i,x\rangle\le b_i,\ i=1,\dots,8\}$ be a bounded polyhedron such that $P$ has nonempty interior and each of the 8 inequalities is irredundant (dropping inequality $i$ lets in a point violating it). So $P$ is a $4$-polytope with exactly $8$ facets, one per inequality. Write $G(P)$ for its vertex–edge graph; $\mathrm{Reach}_k(u,v)$ means that $u,v$ are joined by a walk of exactly $k$ steps, each step being either stationary or along an edge of $P$ (equivalently $\operatorname{dist}_{G(P)}(u,v)\le k$).
--
--   Let $u,v$ be vertices of $P$ lying on a common facet. Then $\mathrm{Reach}_4(u,v)$, i.e. $u$ and $v$ are at distance at most $4$ in $G(P)$.
--
--   Mathematically it follows from the three-dimensional Hirsch bound applied inside the common facet (a $3$-polytope with at most $7$ facets has diameter at most $4$, and edges of a facet are edges of $P$); the formal statement avoids the face-lattice machinery by asking directly for a walk in $P$.
--
--   **Formalization Note** `Hirsch.Hpoly a b` is the set of $x$ with `⟪a i, x⟫ ≤ b i` for all `i`; `SantosHirsch.Counter.IsFacetPresentation a b` says that its interior is nonempty and that every row is irredundant; `Bornology.IsBounded` is boundedness; `Set.extremePoints ℝ` are the vertices; `Hirsch.Reach P k u v` is a walk `w 0 = u, …, w k = v` with each step stationary or `Hirsch.Adj` (the segment is an extreme subset, i.e. an edge); `SantosHirsch.Counter.IsSpindle a b u v` says that `u ≠ v` are vertices and every row is tight at exactly one of them (platform definitions).
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `HirschDim4.h8_4_bound` (every $4$-polytope with $8$ facets has combinatorial diameter at most $4$; milestone of the mission `HirschDim4.counterexample_dim4`). For $n\le 2d$ facets, two distinct vertices either share a facet or have disjoint facet sets; a vertex lies on at least $d$ facets (proved in Lean: an extreme point of an H-polyhedron has at least $d$ tight rows, otherwise one moves along a direction orthogonal to them), so with $n=2d$ disjoint facet sets cover all rows and the pair is a spindle. The verified reduction proves the base statement from this statement together with its companion `dim4_spindle_eight_facets` (spindles). This statement is the common-facet case: a special case of the base statement (same conclusion, stronger hypothesis on the pair).
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). V. Klee and D. W. Walkup, The $d$-step conjecture for polyhedra of dimension $d<6$, Acta Math. 117 (1967), 53–78 (they prove $\Delta_b(d,2d)=d$ for $d\le 5$, in particular $\Delta_b(4,8)=4$) and V. Klee, Diameters of polyhedral graphs, Canad. J. Math. 16 (1964), 602–614 (Hirsch bound in dimension $3$). Origin of this statement: it is the missing step (together with `dim4_spindle_eight_facets`) of a reduction of HirschDim4.h8_4_bound, a milestone of the mission HirschDim4.counterexample_dim4.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_SantosHirsch_Counter_Setting

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace LefebvreVariations

theorem dim4_common_facet_eight_facets (a : Fin 8 → EuclideanSpace ℝ (Fin 4)) (b : Fin 8 → ℝ)
    (u v : EuclideanSpace ℝ (Fin 4))
    (hfp : SantosHirsch.Counter.IsFacetPresentation a b)
    (hbd : Bornology.IsBounded (Hirsch.Hpoly a b))
    (hu : u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hcomm : ∃ i, ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i) :
    Hirsch.Reach (Hirsch.Hpoly a b) 4 u v := by
  sorry

end LefebvreVariations
