-- Prove2me | Theorems.Thm_OAI_MainGap_conditional_defect_bounds
-- name    : OAI.MainGap.conditional_defect_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:33:44.571429+00:00
-- url     : https://prove2.me/theorems/26a9abb7-35aa-4ec5-9923-05ff18950050
-- title:
--   Order bounds $0\le y(1-c^*p^2c)y\le y^2\le1$ for contractions $p,y\ge0$ and $c$
-- statement:
--   Let $A$ be a unital C*-algebra, ordered by its cone of positive elements. Let $p,y,c\in A$ with
--   $$
--   p\ge0,\qquad y\ge0,\qquad \|p\|\le1,\qquad \|y\|\le1,\qquad \|c\|\le1 .
--   $$
--   Then the *defect* $d=y(1-c^*p^2c)y$ satisfies
--   $$
--   0\ \le\ y(1-c^*p^2c)y\ \le\ y^2\ \le\ 1 .
--   $$
--
--   The defect measures how far $c^*p^2c$ is from acting as the identity on $y$. The lemma records that it is a positive element dominated by $y^2$, and that $y^2$ is a positive contraction. These order facts are the starting point of all later estimates on the defect: the norm-loss bound on the hereditary subalgebra of $y(d-\delta)_+y$ and the criterion $\|d\|\le\delta$ when that compression vanishes.
--
--   **Formalization Note** The algebra carries an arbitrary partial order making it a star-ordered ring, which for a C*-algebra is the usual order; $c^*$ is `star c` and $p^2$ is written `p*p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Compression.lean#L136-L155

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

theorem OAI.MainGap.conditional_defect_bounds {p y c : A} (hp : 0 ≤ p) (hy : 0 ≤ y)
    (hpn : ‖p‖ ≤ 1) (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1) :
    0 ≤ y*(1-star c*(p*p)*c)*y ∧
    y*(1-star c*(p*p)*c)*y ≤ y*y ∧ y*y ≤ 1 := by sorry
