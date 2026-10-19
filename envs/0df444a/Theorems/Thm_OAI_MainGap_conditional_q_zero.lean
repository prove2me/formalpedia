-- Prove2me | Theorems.Thm_OAI_MainGap_conditional_q_zero
-- name    : OAI.MainGap.conditional_q_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:36:03.580551+00:00
-- url     : https://prove2.me/theorems/7d820f73-fe06-4ff5-b952-007f4a7ebe43
-- title:
--   If $y\,(d-\delta)_+\,y=0$ then the defect $d=y(1-c^*p^2c)y$ has norm at most $\delta$
-- statement:
--   Let $A$ be a unital C*-algebra, ordered by its cone of positive elements, and for a self-adjoint $e$ let $(e-\delta)_+$ be the functional-calculus cut-down by $t\mapsto\max(t-\delta,0)$.
--
--   Let $p,y,c\in A$ with $p\ge0$, $y\ge0$, $\|p\|\le1$, $\|y\|\le1$ and $\|c\|\le1$, let $\delta>0$, and put $d=y(1-c^*p^2c)y$. Then
--   $$
--   y\,(d-\delta)_+\,y=0\quad\Longrightarrow\quad\|d\|\le\delta .
--   $$
--
--   The compression $q=y(d-\delta)_+y$ can vanish only if the defect is uniformly at most $\delta$. In the shrinking step this is applied inside a representation $\pi$: if $\pi(q)=0$ then $\|\pi(d)\|\le\delta$. The quantitative nonvanishing bound then forces $\pi(y)$ to be small, so $q$ can serve as a signal for $y$.
--
--   **Formalization Note** The algebra carries an arbitrary partial order making it a star-ordered ring, which for a C*-algebra is the usual order; $(d-\delta)_+$ is `cut d δ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Compression.lean#L214-L242

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
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Nonvanishing
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Compression

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem OAI.MainGap.conditional_q_zero {p y c : A} (hp : 0 ≤ p) (hy : 0 ≤ y)
    (hpn : ‖p‖ ≤ 1) (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hq : y*cut (y*(1-star c*(p*p)*c)*y) δ*y=0) :
    ‖y*(1-star c*(p*p)*c)*y‖ ≤ δ := by sorry
