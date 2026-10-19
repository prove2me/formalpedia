-- Prove2me | Theorems.Thm_OAI_MainGap_exists_rep_killing_ideal
-- name    : OAI.MainGap.exists_rep_killing_ideal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:45:15.52969+00:00
-- url     : https://prove2.me/theorems/4e2b4034-9c3a-4f3e-a15e-5d45c26bd4f9
-- title:
--   A Hilbert space representation separating an element from a closed ideal
-- statement:
--   Let $A$ be a unital C*-algebra and let $J\subseteq A$ be a closed two-sided ideal; precisely, $J$ is a $*$-subalgebra (closed under addition, multiplication, multiplication by complex scalars and adjoints) which is norm closed and satisfies $bz\in J$ and $zb\in J$ for all $b\in A$ and $z\in J$. Let $a\in A$ with $a\notin J$. Then there exist a complex Hilbert space $H$ and a unital $*$-homomorphism $\pi:A\to B(H)$ such that
--   $$\pi(z)=0\ \text{ for all } z\in J\qquad\text{and}\qquad \pi(a)\neq0.$$
--
--   Equivalently, every closed two-sided ideal of $A$ is the intersection of the kernels of the representations of $A$ that annihilate it, so membership in $J$ can be tested one representation at a time. This is how ideal membership is detected in arguments formulated through norm conditions in all representations.
--
--   **Formalization Note** The representation is an element of `HilbertRep.{u,u} A`, so the Hilbert space lives in the same universe as $A$. The ideal is a `NonUnitalStarSubalgebra ℂ A` with closedness and the two absorption properties as separate hypotheses. The order instances on $A$ are an arbitrary star-ordering (on a C*-algebra this is the usual order); they do not occur in the statement and are only used for positive functionals in the proof.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/IdealDetection.lean#L40-L113

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
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealDetection

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem OAI.MainGap.exists_rep_killing_ideal (J : NonUnitalStarSubalgebra ℂ A)
    (hJ : IsClosed (J : Set A))
    (hleft : ∀ a : A, ∀ z ∈ J, a * z ∈ J)
    (hright : ∀ a : A, ∀ z ∈ J, z * a ∈ J)
    {a : A} (ha : a ∉ J) :
    ∃ R : HilbertRep.{u,u} A, (∀ z ∈ J, R.hom z = 0) ∧ R.hom a ≠ 0 := by sorry
