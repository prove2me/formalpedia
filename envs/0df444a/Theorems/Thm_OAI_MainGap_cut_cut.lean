-- Prove2me | Theorems.Thm_OAI_MainGap_cut_cut
-- name    : OAI.MainGap.cut_cut
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:18:22.535183+00:00
-- url     : https://prove2.me/theorems/cd4ba1bf-053f-4afc-bdd2-4a5431637908
-- title:
--   Iterated cut-downs add up: $((a-l)_+-u)_+=(a-(l+u))_+$
-- statement:
--   Let $A$ be a C*-algebra (not necessarily unital) with its usual order. For a self-adjoint element $a\in A$ and $\varepsilon\in\mathbb{R}$ define the cut-down
--
--   $$
--   (a-\varepsilon)_+=f_\varepsilon(a),\qquad f_\varepsilon(t)=\max(t-\varepsilon,0),
--   $$
--
--   using the (non-unital) continuous functional calculus.
--
--   **Theorem.** If $a\ge0$ and $l,u\in\mathbb{R}$ satisfy $l\ge0$ and $u\ge0$, then
--
--   $$
--   \big((a-l)_+-u\big)_+=\big(a-(l+u)\big)_+.
--   $$
--
--   This identity allows nested cut-downs to be rewritten as a single one, for instance $((R-\eta)_+-\eta)_+=(R-2\eta)_+$, which is how elements built from a cut-down are located in hereditary subalgebras of further cut-downs.
--
--   **Formalization Note** The cut-down is `cut a ε`, defined as `cfcₙ (fun t => max (t - ε) 0) a`. The order on $A$ is an arbitrary partial order making $A$ a star-ordered ring, which in a C*-algebra is the usual order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Cutoffs.lean#L156-L175

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
variable {A : Type*} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

theorem OAI.MainGap.cut_cut {a : A} (ha : 0 ≤ a) {l u : ℝ} (hl : 0 ≤ l) (hu : 0 ≤ u) :
    cut (cut a l) u = cut a (l+u) := by sorry
