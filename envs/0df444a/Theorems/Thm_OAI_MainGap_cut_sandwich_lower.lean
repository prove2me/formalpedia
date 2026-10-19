-- Prove2me | Theorems.Thm_OAI_MainGap_cut_sandwich_lower
-- name    : OAI.MainGap.cut_sandwich_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:09:43.318801+00:00
-- url     : https://prove2.me/theorems/d07e025e-7aef-4200-87d5-6c62219be132
-- title:
--   The positive part $(d-\varepsilon)_+$ satisfies $\varepsilon\,(d-\varepsilon)_+^2\le(d-\varepsilon)_+\,d\,(d-\varepsilon)_+$
-- statement:
--   Let $A$ be a possibly non-unital C$^*$-algebra, ordered by its positive cone. For a self-adjoint $d\in A$ and $\varepsilon\ge0$ let
--   $$(d-\varepsilon)_+=f_\varepsilon(d),\qquad f_\varepsilon(t)=\max(t-\varepsilon,0),$$
--   be defined by the continuous functional calculus. The non-unital calculus applies because $f_\varepsilon(0)=0$.
--
--   **Theorem.** If $d\in A$ is self-adjoint and $\varepsilon\ge0$, then
--   $$\varepsilon\,(d-\varepsilon)_+^{2}\ \le\ (d-\varepsilon)_+\,d\,(d-\varepsilon)_+ .$$
--
--   In words, on the range of the cut-down $(d-\varepsilon)_+$ the element $d$ is at least $\varepsilon$. This is the lower bound behind the comparison lemma for cut-downs. If $\|d-s^*vs\|<\varepsilon$, then $(d-\varepsilon)_+\,s^*vs\,(d-\varepsilon)_+$ still dominates a positive multiple of $(d-\varepsilon)_+^2$, so the hereditary subalgebra of $(d-\varepsilon)_+$ can be transported into that of $v$.
--
--   **Formalization Note** $(d-\varepsilon)_+$ is `cut d ε = cfcₙ (fun t => max (t - ε) 0) d`, and $\varepsilon\,(\cdot)$ is real scalar multiplication. The order on $A$ is any partial order making $A$ a star-ordered ring, which is necessarily the positive-cone order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Hereditary.lean#L514-L538

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
variable {A : Type*} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

theorem OAI.MainGap.cut_sandwich_lower {d : A} (hd : IsSelfAdjoint d) {ε : ℝ} (hε : 0 ≤ ε) :
    ε • (cut d ε * cut d ε) ≤ cut d ε * d * cut d ε := by sorry
