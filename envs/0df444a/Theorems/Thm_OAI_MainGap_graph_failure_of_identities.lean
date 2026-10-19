-- Prove2me | Theorems.Thm_OAI_MainGap_graph_failure_of_identities
-- name    : OAI.MainGap.graph_failure_of_identities
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:27:45.087318+00:00
-- url     : https://prove2.me/theorems/e4e2393d-207c-4340-a496-c3102ed3d3dc
-- title:
--   A vanishing graph defect forces the measurements to recover $T_0,\dots,T_3$ and $\|X\|=\|y\|$
-- statement:
--   Let $D$ be a unital C*-algebra, ordered by its cone of positive elements. For $h\in D$ let $\mathrm{Her}(h)=\overline{\{hah^*: a\in D\}}$. For a positive $X\in D$ let $(X-\tfrac1{32})_+$ and $g(X)$ be defined by continuous functional calculus from $t\mapsto\max(t-\tfrac1{32},0)$ and from the cut-off inverse $g(s)=s/\max(\tfrac1{32},s)^2$; thus $g(0)=0$ and $g(s)=1/s$ for $s\ge\tfrac1{32}$. Square roots $t^{1/2}$ are positive square roots.
--
--   Let $t,z\in D$ with $t\ge0$, $\|t\|\le1$ and $z^*z=t$. Let $w_0,\dots,w_5\in D$ and $T_0,\dots,T_3\in D$ satisfy
--   $$
--   w_0^*z=\tfrac14\,t\,t^{1/2},\qquad w_{i+1}^*z=\tfrac14\,t\,T_i\,t^{1/2}\quad(i=0,1,2,3).
--   $$
--   Let $c,y\in D$ with $y\ge0$ and $\|c\|\le1$, put $F=cyc^*$, and define the *measurements*
--   $$
--   X=16\,w_0^*Fw_0,\qquad B_i=16\,w_{i+1}^*Fw_0\,g(X)\quad(i=0,1,2,3).
--   $$
--   Assume that $T_i\in\mathrm{Her}\big((X-\tfrac1{32})_+\big)$ for every $i$ and that the defect vanishes, $y\big(1-c^*(zz^*)^2c\big)y=0$. Then
--   $$
--   \|X\|=\|y\|\qquad\text{and}\qquad B_i=T_i\quad\text{for } i=0,1,2,3.
--   $$
--   (The element $w_5$ is unconstrained and plays no role.)
--
--   This is the algebraic core of the graph construction. There $z$ is a "graph" of the $T_i$ assembled from orthogonal slots $w_j$ and $p=zz^*$. The identities are applied inside a representation: if the defect $y(1-c^*p^2c)y$ vanishes there, the representation sees $X$ with the norm of $y$ and sees each measurement $B_i$ equal to $T_i$. The four-element avoidance theorem excludes exactly this coincidence when $\|X\|>1/4$.
--
--   **Formalization Note** The measurements are `measurementX (w 0) F` and `measurementB w F i`, where the slot index `i.castSucc.succ` is $i+1$; $g$ is `graphInverseFn` and $g(X)$ is `graphInverse X`. The algebra carries an arbitrary partial order making it a star-ordered ring, which for a C*-algebra is the usual order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Graph.lean#L447-L517

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Graph

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
variable {A : Type*} [NonUnitalCStarAlgebra A]
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem OAI.MainGap.graph_failure_of_identities {t z : D} (ht : 0 ≤ t) (htn : ‖t‖ ≤ 1)
    (w : Fin 6 → D) (hz : star z*z=t) (T : Fin 4 → D)
    (hW₀ : star (w 0)*z=(1/4 : ℝ) • (t*CFC.sqrt t))
    (hWi : ∀ i : Fin 4, star (w i.castSucc.succ)*z=(1/4 : ℝ) • (t*T i*CFC.sqrt t))
    (c y : D) (hy : 0 ≤ y) (hcn : ‖c‖ ≤ 1)
    (hTX : ∀ i, T i ∈ Her (cut (measurementX (w 0) (c*y*star c)) (1/32)))
    (hd : y*(1-star c*((z*star z)*(z*star z))*c)*y=0) :
    ‖measurementX (w 0) (c*y*star c)‖=‖y‖ ∧ ∀ i, measurementB w (c*y*star c) i=T i := by sorry
