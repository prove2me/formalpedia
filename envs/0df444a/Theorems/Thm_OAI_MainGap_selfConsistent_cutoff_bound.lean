-- Prove2me | Theorems.Thm_OAI_MainGap_selfConsistent_cutoff_bound
-- name    : OAI.MainGap.selfConsistent_cutoff_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:21:02.897394+00:00
-- url     : https://prove2.me/theorems/7ed5c7be-9553-4a19-b14e-230738a449c9
-- title:
--   A self-consistent hereditary cutoff condition forces the bound $d\le h\cdot 1$
-- statement:
--   Let $B$ be a unital C*-algebra with its usual order. For a self-adjoint $c\in B$ and $\varepsilon\in\mathbb{R}$ let $(c-\varepsilon)_+$ denote $\max(t-\varepsilon,0)$ applied to $c$ by continuous functional calculus, and for $y\in B$ let $\operatorname{Her}(y)=\overline{yBy^*}$ be the norm closure of $\{yby^*: b\in B\}$.
--
--   **Theorem.** Let $x,d\in B$ be positive, let $\eta>0$ and $h\ge0$ be real numbers, and put
--
--   $$
--   Q=(h-d)_+:=q(d),\qquad q(t)=\max(h-t,0).
--   $$
--
--   If
--
--   $$
--   d\in\operatorname{Her}\big((xQ^2x-\eta)_+\big),
--   $$
--
--   then $d\le h\cdot1$; equivalently, the spectrum of $d$ is contained in $[0,h]$, or $\|d\|\le h$.
--
--   The hypothesis is self-referential: $d$ is required to lie under a cut-down of $xQ^2x$, where $Q$ is built from $d$ itself and vanishes on the part of the spectrum of $d$ above $h$. The lemma shows that this is only possible if $d$ has no spectrum above $h$, converting a hereditary-membership condition into an explicit order bound. A typical application takes $h=\tfrac12$ and $d=BB^*$, so that $Q=(\tfrac12-BB^*)_+$, and concludes $BB^*\le\tfrac12\cdot1$ from the fact that $BB^*$ lies under a cut-down of $x\,(\tfrac12-BB^*)_+^2\,x$.
--
--   **Formalization Note** Here $h$ is a real scalar. $Q$ is written `cfc (fun t => max (h - t) 0) d` (unital functional calculus), $xQ^2x$ is `x * Q * Q * x`, the cut-down is `cut _ η`, and the conclusion is `d ≤ h • (1 : B)`. The order on $B$ is an arbitrary partial order making $B$ a star-ordered ring, which in a C*-algebra is the usual order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Cutoffs.lean#L300-L335

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
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem OAI.MainGap.selfConsistent_cutoff_bound {x d : B} (hx : 0 ≤ x) (hd : 0 ≤ d)
    {η h : ℝ} (hη : 0 < η) (hh : 0 ≤ h)
    (hmem : d ∈ Her (cut (x * cfc (fun t : ℝ => max (h - t) 0) d *
      cfc (fun t : ℝ => max (h - t) 0) d * x) η)) :
    d ≤ h • (1 : B) := by sorry
