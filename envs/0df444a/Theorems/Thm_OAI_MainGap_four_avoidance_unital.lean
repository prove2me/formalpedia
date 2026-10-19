-- Prove2me | Theorems.Thm_OAI_MainGap_four_avoidance_unital
-- name    : OAI.MainGap.four_avoidance_unital
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:27:02.712292+00:00
-- url     : https://prove2.me/theorems/78a33182-5b84-42c4-8086-5efa113ae691
-- title:
--   Avoidance lemma: four contractions under $(X-1/32)_+$ that no representation with $\|\pi(X)\|>1/4$ can match with four given elements
-- statement:
--   Let $A$ be a unital C*-algebra, ordered by its cone of positive elements. For a positive $X\in A$ and $\varepsilon\ge0$ let $(X-\varepsilon)_+=f_\varepsilon(X)$, where $f_\varepsilon(t)=\max(t-\varepsilon,0)$ is applied by continuous functional calculus. For $h\in A$ let $\mathrm{Her}(h)=\overline{\{hah^*: a\in A\}}$ be the norm closure of the "sandwiches" $hah^*$ (for positive $h$ this is the hereditary C*-subalgebra $\overline{hAh}$). An element $z\in A$ is *properly infinite* if $\operatorname{diag}(z,z)$ is Cuntz-below $z$ inside $2\times2$ matrices: there is a sequence of $1\times2$ matrices $r_j$ over $A$ with $r_j^*\,z\,r_j\to\operatorname{diag}(z,z)$ in $M_2(A)$ (equivalently, there are $x_j,y_j\in A$ with $x_j^*zx_j\to z$, $y_j^*zy_j\to z$ and $x_j^*zy_j\to0$). A *representation* of $A$ is a unital $*$-homomorphism $\pi\colon A\to B(H)$ into the bounded operators on a complex Hilbert space $H$.
--
--   Let $X\in A$ be positive and let $B_0,B_1,B_2,B_3\in A$ be arbitrary. Assume that every positive element of $\mathrm{Her}\big((X-\tfrac1{32})_+\big)$ is properly infinite. Then there exist $T_0,T_1,T_2,T_3\in\mathrm{Her}\big((X-\tfrac1{32})_+\big)$ with $\|T_j\|\le1$ for every $j$ such that, for every representation $\pi$ of $A$,
--   $$
--   \|\pi(X)\|>\tfrac14\quad\Longrightarrow\quad \pi(T_j)\neq\pi(B_j)\ \text{ for at least one } j\in\{0,1,2,3\}.
--   $$
--
--   Thus one quadruple of contractions, living where $X$ exceeds $1/32$ and chosen independently of the representation, can never be confused with the prescribed quadruple $(B_j)$ in a representation in which $X$ is large. This avoidance principle feeds the graph construction of the shrinking step: there the $B_j$ are measurements of a defect, and avoidance rules out that the defect vanishes in a representation where it should be visible.
--
--   **Formalization Note** The order on $A$ is the spectral order `CStarAlgebra.spectralOrder`; proper infiniteness is `OAI.MainGap.ProperlyInfinite`, i.e. `FiniteCuntzLE (doubleCorner z) (scalarCorner z)`; the algebra $\mathrm{Her}((X-1/32)_+)$ is `fourHer X`. Representations are the structures `HilbertRep.{u,v} A`: a complex Hilbert space in a fixed (arbitrary) universe `v` together with a unital star-algebra homomorphism from $A$ into its bounded operators.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Avoidance.lean#L114-L182

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

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
universe u v
open Filter
open scoped Topology
attribute [local instance] OAI.MainGap.avoidancePartialOrder
attribute [local instance] OAI.MainGap.avoidanceStarOrderedRing
attribute [local instance] OAI.MainGap.avoidanceOperatorPartialOrder
attribute [local instance] OAI.MainGap.avoidanceOperatorStarOrderedRing
variable (A : Type u) [CStarAlgebra A]
variable {A}

theorem OAI.MainGap.four_avoidance_unital {X : A} (hX : 0 ≤ X) (B : Fin 4 → A)
    (hp : ∀ z : A, 0 ≤ z → z ∈ fourHer X → ProperlyInfinite z) :
    ∃ T : Fin 4 → A, (∀ j, ‖T j‖ ≤ 1) ∧ (∀ j, T j ∈ fourHer X) ∧
      ∀ R : HilbertRep.{u,v} A, (1/4 : ℝ) < ‖R.hom X‖ →
        ¬ ∀ j, R.hom (T j) = R.hom (B j) := by sorry
