-- Prove2me | Theorems.Thm_OAI_MainGap_shrinking_nonunital
-- name    : OAI.MainGap.shrinking_nonunital
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:39:51.618047+00:00
-- url     : https://prove2.me/theorems/11e7a8ec-8f36-4639-802c-00d47200eddf
-- title:
--   Shrinking lemma: strict hereditary compression with norm signals under Property P
-- statement:
--   Let $A$ be a C*-algebra, not necessarily unital, with its usual order, and let $\tilde A$ be its unitization. We use the following notions.
--
--   - For $h\in A$, $\operatorname{Her}(h)=\overline{\{\,h\,b\,h^*:\ b\in A\,\}}$.
--   - An element $h\in A$ is *properly infinite* if there are row matrices $r_j=(r_j^{(1)},r_j^{(2)})$ with entries in $A$, $j\in\mathbb{N}$, such that $r_j^*\,h\,r_j=\bigl((r_j^{(k)})^*\,h\,r_j^{(l)}\bigr)_{k,l=1,2}$ converges to $\operatorname{diag}(h,h)$ in the C*-algebra $M_2(A)$. The algebra $A$ has *Property P* if every positive element of $A$ is properly infinite.
--   - For $a,p\in A$, $p$ *carries the norm signal of* $a$ if $\|\pi(p)\|=1$ for every unital $*$-homomorphism $\pi:\tilde A\to B(H)$, $H$ a complex Hilbert space, with $\|\pi(a)\|>\tfrac12$.
--
--   Assume that $A$ has Property P, and let $a,y,c\in A$ with $a\ge0$, $y\ge0$, $\|y\|\le1$ and $\|c\|\le1$. Then there exist $p,q\in A$ and $\kappa\in\mathbb{R}$ with
--   $$0\le p,\quad\|p\|\le1,\quad p\in\operatorname{Her}(a),\qquad 0\le q,\quad\|q\|\le1,\quad q\in\operatorname{Her}(y),\qquad 0\le\kappa<1,$$
--   $$\|x\,c\,k\|\le\kappa\,\|x\|\,\|k\|\qquad\text{for all }x\in\operatorname{Her}(p),\ k\in\operatorname{Her}(q),$$
--   such that $p$ carries the norm signal of $a$ and $q$ carries the norm signal of $y$.
--
--   This is one shrinking step for an arbitrary pair of positive elements: inside the hereditary subalgebras of $a$ and $y$ one finds smaller ones between which $c$ acts strictly contractively, without losing the parts of $a$ and $y$ of norm above $\tfrac12$ in any representation. It is the input for the uniform and iterated separation results that lead to the diagonalization property in the main theorem.
--
--   **Formalization Note** Property P is `PropertyP A` from the comparison module: each positive $h$ satisfies `FiniteCuntzLE (doubleCorner h) (scalarCorner h)`, a comparison by finite $1\times2$ matrices rather than in the stabilization. The norm signal is `NormSignal a p`, which quantifies over `HilbertRep.{u,u} (Unitization ℂ A)`, i.e. Hilbert spaces in the universe of $A$. The orders on $A$ and $\tilde A$ are the spectral orders. No bound on $\|a\|$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Shrinking.lean#L205-L239

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

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
universe u
attribute [local instance] OAI.MainGap.shrinkingNonunitalPartialOrder
attribute [local instance] OAI.MainGap.shrinkingNonunitalStarOrderedRing
attribute [local instance] OAI.MainGap.shrinkingNonunitalUnitizationPartialOrder
attribute [local instance] OAI.MainGap.shrinkingNonunitalUnitizationStarOrderedRing
variable {A : Type u} [NonUnitalCStarAlgebra A]

theorem OAI.MainGap.shrinking_nonunital (hp : PropertyP A) {a y c : A} (ha : 0 ≤ a) (hy : 0 ≤ y)
    (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1) :
    ∃ (p q : A) (κ : ℝ), 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ p ∈ Her a ∧
      0 ≤ q ∧ ‖q‖ ≤ 1 ∧ q ∈ Her y ∧ 0 ≤ κ ∧ κ < 1 ∧
      HerCompression p q c κ ∧ NormSignal a p ∧ NormSignal y q := by sorry
