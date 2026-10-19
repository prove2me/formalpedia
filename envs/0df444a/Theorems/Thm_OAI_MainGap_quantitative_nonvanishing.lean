-- Prove2me | Theorems.Thm_OAI_MainGap_quantitative_nonvanishing
-- name    : OAI.MainGap.quantitative_nonvanishing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:30:23.325737+00:00
-- url     : https://prove2.me/theorems/9442f563-6a10-4520-a820-66b24aa960ae
-- title:
--   Quantitative nonvanishing: if $\pi(d)=0$ forces $\|\pi(y)\|\le1/4$, then $\|\pi(y)\|>3/8$ forces $\|\pi(d)\|>\delta$ uniformly
-- statement:
--   Let $A$ be a unital C*-algebra, ordered by its cone of positive elements. A *representation* of $A$ is a unital $*$-homomorphism $\pi\colon A\to B(H)$ into the bounded operators on a complex Hilbert space $H$; norms $\|\pi(\cdot)\|$ are operator norms.
--
--   Let $d,y\in A$ with $y\ge0$, and assume that every representation annihilating $d$ makes $y$ small: for every representation $\pi$, $\pi(d)=0$ implies $\|\pi(y)\|\le\tfrac14$. Then there is a constant $\delta$ with $0<\delta<1$ such that, for every representation $\pi$ of $A$,
--   $$
--   \|\pi(y)\|>\tfrac38\quad\Longrightarrow\quad\|\pi(d)\|>\delta .
--   $$
--
--   The theorem upgrades a qualitative implication ("$d$ vanishes only where $y$ is small") to a uniform quantitative one: wherever $y$ is noticeably large, $d$ is bounded away from zero, with one $\delta$ for all representations. Note the strict gap between the two thresholds $1/4$ and $3/8$. In the shrinking step it is applied to the defect $d=y(1-c^*p^2c)y$ produced by the graph construction.
--
--   **Formalization Note** Representations are `HilbertRep.{u,u} A`, i.e. the Hilbert spaces live in the same universe as $A$. The order on $A$ and on operators is `CStarAlgebra.spectralOrder`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Nonvanishing.lean#L33-L81

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

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
universe u v
attribute [local instance] OAI.MainGap.nonvanishingPartialOrder
attribute [local instance] OAI.MainGap.nonvanishingStarOrderedRing
attribute [local instance] OAI.MainGap.nonvanishingOperatorPartialOrder
attribute [local instance] OAI.MainGap.nonvanishingOperatorStarOrderedRing
variable {A : Type u} [CStarAlgebra A]

theorem OAI.MainGap.quantitative_nonvanishing {d y : A} (hy : 0 ≤ y)
    (h : ∀ R : HilbertRep.{u,u} A, R.hom d=0 → ‖R.hom y‖ ≤ (1/4 : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ R : HilbertRep.{u,u} A,
      (3/8 : ℝ) < ‖R.hom y‖ → δ < ‖R.hom d‖ := by sorry
