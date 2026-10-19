-- Prove2me | Theorems.Thm_OAI_MainGap_iterated_separation
-- name    : OAI.MainGap.iterated_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:43:27.726553+00:00
-- url     : https://prove2.me/theorems/7590966f-2fd0-4ece-8e9b-aabe8a744409
-- title:
--   Iterated separation: arbitrarily small hereditary compression constants under Property P
-- statement:
--   Let $A$ be a C*-algebra, not necessarily unital, with its usual order, and let $\tilde A$ be its unitization. We use the following notions.
--
--   - For $h\in A$, $\operatorname{Her}(h)=\overline{\{\,h\,b\,h^*:\ b\in A\,\}}$.
--   - An element $h\in A$ is *properly infinite* if there are row matrices $r_j=(r_j^{(1)},r_j^{(2)})$ with entries in $A$, $j\in\mathbb{N}$, such that $r_j^*\,h\,r_j=\bigl((r_j^{(k)})^*\,h\,r_j^{(l)}\bigr)_{k,l=1,2}$ converges to $\operatorname{diag}(h,h)$ in $M_2(A)$. The algebra $A$ has *Property P* if every positive element of $A$ is properly infinite.
--   - For $a,p\in A$, $p$ *carries the norm signal of* $a$ if $\|\pi(p)\|=1$ for every unital $*$-homomorphism $\pi:\tilde A\to B(H)$, $H$ a complex Hilbert space, with $\|\pi(a)\|>\tfrac12$.
--
--   Assume that $A$ has Property P. Let $a,b,c\in A$ with $a\ge0$, $\|a\|\le1$, $b\ge0$, $\|b\|\le1$, $\|c\|\le1$, and let $\zeta>0$. Then there exist $p,q\in A$ and $\kappa\in\mathbb{R}$ with
--   $$0\le p,\quad\|p\|\le1,\quad p\in\operatorname{Her}(a),\qquad 0\le q,\quad\|q\|\le1,\quad q\in\operatorname{Her}(b),\qquad 0\le\kappa<\zeta,$$
--   $$\|x\,c\,k\|\le\kappa\,\|x\|\,\|k\|\qquad\text{for all }x\in\operatorname{Her}(p),\ k\in\operatorname{Her}(q),$$
--   such that $p$ carries the norm signal of $a$ and $q$ carries the norm signal of $b$.
--
--   In words, $c$ can be made arbitrarily small between suitable hereditary subalgebras of $a$ and $b$ that still detect every representation in which $a$, respectively $b$, has norm above $\tfrac12$. This approximate separation is the ingredient that makes the cross term $s^*ct$ small in the diagonalization property of the main theorem.
--
--   **Formalization Note** Property P is `PropertyP A` from the comparison module (finite $1\times2$ matrix comparison `FiniteCuntzLE (doubleCorner h) (scalarCorner h)`), the compression condition is `HerCompression p q c κ`, and the norm signal is `NormSignal a p`, quantifying over `HilbertRep.{u,u} (Unitization ℂ A)`. Orders are the spectral orders.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Separation.lean#L66-L109

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
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Shrinking
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Products
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Separation

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
universe u
attribute [local instance] OAI.MainGap.separationPartialOrder
attribute [local instance] OAI.MainGap.separationStarOrderedRing
variable {A : Type u} [NonUnitalCStarAlgebra A]

theorem OAI.MainGap.iterated_separation (hp : PropertyP A) {a b c : A} (ha : 0 ≤ a) (han : ‖a‖ ≤ 1)
    (hb : 0 ≤ b) (hbn : ‖b‖ ≤ 1) (hcn : ‖c‖ ≤ 1) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ (p q : A) (κ : ℝ), 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ p ∈ Her a ∧
      0 ≤ q ∧ ‖q‖ ≤ 1 ∧ q ∈ Her b ∧ 0 ≤ κ ∧ κ < ζ ∧
      HerCompression p q c κ ∧ NormSignal a p ∧ NormSignal b q := by sorry
