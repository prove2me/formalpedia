-- Prove2me | Theorems.Thm_OAI_MainGap_uniform_shrinking
-- name    : OAI.MainGap.uniform_shrinking
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:42:24.769066+00:00
-- url     : https://prove2.me/theorems/dbf475c7-417e-4066-8579-9b1560090919
-- title:
--   Uniform shrinking constant for hereditary compression under Property P
-- statement:
--   Let $A$ be a C*-algebra, not necessarily unital, with its usual order, and let $\tilde A$ be its unitization. We use the following notions.
--
--   - For $h\in A$, $\operatorname{Her}(h)=\overline{\{\,h\,b\,h^*:\ b\in A\,\}}$.
--   - An element $h\in A$ is *properly infinite* if there are row matrices $r_j=(r_j^{(1)},r_j^{(2)})$ with entries in $A$, $j\in\mathbb{N}$, such that $r_j^*\,h\,r_j=\bigl((r_j^{(k)})^*\,h\,r_j^{(l)}\bigr)_{k,l=1,2}$ converges to $\operatorname{diag}(h,h)$ in $M_2(A)$. The algebra $A$ has *Property P* if every positive element of $A$ is properly infinite.
--   - For $a,p\in A$, $p$ *carries the norm signal of* $a$ if $\|\pi(p)\|=1$ for every unital $*$-homomorphism $\pi:\tilde A\to B(H)$, $H$ a complex Hilbert space, with $\|\pi(a)\|>\tfrac12$.
--
--   Assume that $A$ has Property P. Then there is a constant $\theta$ with $0<\theta<1$ such that for all $a,y,c\in A$ with $a\ge0$, $\|a\|\le1$, $y\ge0$, $\|y\|\le1$ and $\|c\|\le1$ there exist $p,q\in A$ with
--   $$0\le p,\quad\|p\|\le1,\quad p\in\operatorname{Her}(a),\qquad 0\le q,\quad\|q\|\le1,\quad q\in\operatorname{Her}(y),$$
--   $$\|x\,c\,k\|\le\theta\,\|x\|\,\|k\|\qquad\text{for all }x\in\operatorname{Her}(p),\ k\in\operatorname{Her}(q),$$
--   such that $p$ carries the norm signal of $a$ and $q$ carries the norm signal of $y$.
--
--   In the shrinking lemma for a single triple $(a,y,c)$ the compression constant $\kappa<1$ depends on the triple; here one constant $\theta$, depending only on $A$, serves every triple in the unit ball. This uniformity is what makes the shrinking step iterable, producing the constants $\theta,\theta^2,\theta^3,\dots$
--
--   **Formalization Note** Property P is `PropertyP A` from the comparison module (finite $1\times2$ matrix comparison `FiniteCuntzLE (doubleCorner h) (scalarCorner h)`), the compression condition is `HerCompression p q c θ`, and the norm signal is `NormSignal a p`, quantifying over `HilbertRep.{u,u} (Unitization ℂ A)` (Hilbert spaces in the universe of $A$). Orders are the spectral orders.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Products.lean#L238-L282

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

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
open scoped ENNReal
universe u
attribute [local instance] OAI.MainGap.sequenceFactorOrder
attribute [local instance] OAI.MainGap.sequenceFactorStarOrder
attribute [local instance] OAI.MainGap.boundedSequenceOrder
attribute [local instance] OAI.MainGap.boundedSequenceStarOrder
variable {A : Type u} [NonUnitalCStarAlgebra A]

theorem OAI.MainGap.uniform_shrinking (hp : PropertyP A) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ a y c : A, 0 ≤ a → ‖a‖ ≤ 1 → 0 ≤ y → ‖y‖ ≤ 1 → ‖c‖ ≤ 1 →
        ∃ p q : A, 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ p ∈ Her a ∧
          0 ≤ q ∧ ‖q‖ ≤ 1 ∧ q ∈ Her y ∧
          HerCompression p q c θ ∧ NormSignal a p ∧ NormSignal y q := by sorry
