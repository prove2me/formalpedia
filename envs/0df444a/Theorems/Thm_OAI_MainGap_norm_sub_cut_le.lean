-- Prove2me | Theorems.Thm_OAI_MainGap_norm_sub_cut_le
-- name    : OAI.MainGap.norm_sub_cut_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:19:54.446248+00:00
-- url     : https://prove2.me/theorems/8dd7e5e9-bb9b-4a2c-8660-67e335029729
-- title:
--   The cut-down $(a-l)_+$ lies within distance $l$ of $a$
-- statement:
--   Let $A$ be a C*-algebra (not necessarily unital) with its usual order. For self-adjoint $a\in A$ and $l\in\mathbb{R}$ let $(a-l)_+=f_l(a)$ with $f_l(t)=\max(t-l,0)$, computed with the continuous functional calculus.
--
--   **Theorem.** If $a\ge0$ and $l\ge0$, then
--
--   $$
--   \big\|a-(a-l)_+\big\|\le l.
--   $$
--
--   This quantifies the cost of cutting down: replacing a positive element by $(a-l)_+$ changes it by at most $l$ in norm. It is used in error estimates such as $\|\pi(U-(U-\eta)_+)\|\le\eta$ for $*$-homomorphisms $\pi$, and, in unital algebras, to deduce $\|a\|\le l$ (hence $a\le l\cdot1$) from $(a-l)_+=0$.
--
--   **Formalization Note** The cut-down is `cut a l`, i.e. `cfcₙ (fun t => max (t - l) 0) a`. The order on $A$ is an arbitrary partial order making $A$ a star-ordered ring, which in a C*-algebra is the usual order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Cutoffs.lean#L177-L192

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

theorem OAI.MainGap.norm_sub_cut_le {a : A} (ha : 0 ≤ a) {l : ℝ} (hl : 0 ≤ l) :
    ‖a - cut a l‖ ≤ l := by sorry
