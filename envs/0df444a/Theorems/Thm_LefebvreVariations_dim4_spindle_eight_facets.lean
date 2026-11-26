-- Prove2me | Theorems.Thm_LefebvreVariations_dim4_spindle_eight_facets
-- name    : LefebvreVariations.dim4_spindle_eight_facets
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:11:40.81363+00:00
-- url     : https://prove2.me/theorems/91614af9-0889-5d56-abdf-5c62b3d09888
-- title:
--   Lefebvre's variations, No. 163 — on a theme by Klee and Walkup: no $4$-spindle with $8$ facets has length above $4$ (the $d$-step statement for $d=4$)
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $P=\{x\in\mathbb{R}^4:\ \langle a_i,x\rangle\le b_i,\ i=1,\dots,8\}$ be a bounded polyhedron such that $P$ has nonempty interior and each of the 8 inequalities is irredundant (dropping inequality $i$ lets in a point violating it). So $P$ is a $4$-polytope with exactly $8$ facets, one per inequality. Write $G(P)$ for its vertex–edge graph; $\mathrm{Reach}_k(u,v)$ means that $u,v$ are joined by a walk of exactly $k$ steps, each step being either stationary or along an edge of $P$ (equivalently $\operatorname{dist}_{G(P)}(u,v)\le k$).
--
--   Let $u\ne v$ be a spindle of $P$: both are vertices and every one of the 8 facets contains exactly one of $u,v$. Then $\mathrm{Reach}_4(u,v)$, i.e. $u$ and $v$ are at distance at most $4$ in $G(P)$.
--
--   This is the $d$-step statement for $d=4$, equivalent (Klee–Walkup) to the Hirsch bound for $8$ facets in dimension $4$. Boundedness is essential: Klee and Walkup's unbounded $4$-dimensional polyhedron with $8$ facets has two vertices at distance $5$ (platform theorem `HirschDim4.unbounded_four_counterexample`).
--
--   **Formalization Note** `Hirsch.Hpoly a b` is the set of $x$ with `⟪a i, x⟫ ≤ b i` for all `i`; `SantosHirsch.Counter.IsFacetPresentation a b` says that its interior is nonempty and that every row is irredundant; `Bornology.IsBounded` is boundedness; `Set.extremePoints ℝ` are the vertices; `Hirsch.Reach P k u v` is a walk `w 0 = u, …, w k = v` with each step stationary or `Hirsch.Adj` (the segment is an extreme subset, i.e. an edge); `SantosHirsch.Counter.IsSpindle a b u v` says that `u ≠ v` are vertices and every row is tight at exactly one of them (platform definitions).
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `HirschDim4.h8_4_bound` (every $4$-polytope with $8$ facets has combinatorial diameter at most $4$; milestone of the mission `HirschDim4.counterexample_dim4`). For $n\le 2d$ facets, two distinct vertices either share a facet or have disjoint facet sets; a vertex lies on at least $d$ facets (proved in Lean: an extreme point of an H-polyhedron has at least $d$ tight rows, otherwise one moves along a direction orthogonal to them), so with $n=2d$ disjoint facet sets cover all rows and the pair is a spindle. The verified reduction proves the base statement from this statement together with its companion `dim4_common_facet_eight_facets` (pairs on a common facet). This statement is the spindle case: a special case of the base statement (same conclusion, stronger hypothesis on the pair).
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). V. Klee and D. W. Walkup, The $d$-step conjecture for polyhedra of dimension $d<6$, Acta Math. 117 (1967), 53–78 (they prove $\Delta_b(d,2d)=d$ for $d\le 5$, in particular $\Delta_b(4,8)=4$). Origin of this statement: it is the missing step (together with `dim4_common_facet_eight_facets`) of a reduction of HirschDim4.h8_4_bound, a milestone of the mission HirschDim4.counterexample_dim4. A pair of vertices of a bounded 4-polytope with 8 facets either lies on a common facet or is a spindle; the reduction, checked in Lean, splits on this.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_SantosHirsch_Counter_Setting

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace LefebvreVariations

theorem dim4_spindle_eight_facets (a : Fin 8 → EuclideanSpace ℝ (Fin 4)) (b : Fin 8 → ℝ)
    (u v : EuclideanSpace ℝ (Fin 4))
    (hfp : SantosHirsch.Counter.IsFacetPresentation a b)
    (hbd : Bornology.IsBounded (Hirsch.Hpoly a b))
    (hsp : SantosHirsch.Counter.IsSpindle a b u v) :
    Hirsch.Reach (Hirsch.Hpoly a b) 4 u v := by
  sorry

end LefebvreVariations
