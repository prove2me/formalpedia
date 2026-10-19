-- Prove2me | Theorems.Thm_OAI_MainGap_lp_nonneg_iff
-- name    : OAI.MainGap.lp_nonneg_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:41:36.403979+00:00
-- url     : https://prove2.me/theorems/bdc460e1-49fd-42b4-8e8a-9219a740c476
-- title:
--   Positivity in an $\ell^\infty$-product of C*-algebras is coordinatewise
-- statement:
--   Let $I$ be an index set and $(E_i)_{i\in I}$ a family of C*-algebras, not necessarily unital. Their $\ell^\infty$-product
--   $$\ell^\infty(I;E)=\Bigl\{\,d=(d_i)_{i\in I}:\ d_i\in E_i,\ \ \|d\|_\infty=\sup_{i\in I}\|d_i\|<\infty\,\Bigr\}$$
--   is a C*-algebra under coordinatewise algebraic operations and the supremum norm. Give each $E_i$ and $\ell^\infty(I;E)$ its canonical C*-order, in which $x\ge0$ means that $x$ is self-adjoint with spectrum contained in $[0,\infty)$. Then for every $d\in\ell^\infty(I;E)$,
--   $$d\ge0\quad\Longleftrightarrow\quad d_i\ge0\ \text{ for every } i\in I.$$
--
--   So positivity in a bounded product can be tested coordinatewise. This allows a uniformly bounded family of positive elements to be assembled into one positive element of $\ell^\infty(\mathbb{N};A)$, which is the basic move in compactness arguments that upgrade statements about a single C*-algebra to statements with uniform constants.
--
--   **Formalization Note** The product is Mathlib's `lp E ∞`, and all orders are `CStarAlgebra.spectralOrder`, installed as local instances; the statement therefore compares the spectral order of the product C*-algebra with the spectral orders of the factors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Products.lean#L121-L134

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
attribute [local instance] OAI.MainGap.productFactorOrder
attribute [local instance] OAI.MainGap.productFactorStarOrder
attribute [local instance] OAI.MainGap.boundedProductOrder
attribute [local instance] OAI.MainGap.boundedProductStarOrder
variable {I : Type*} {E : I → Type*} [∀ i, NonUnitalCStarAlgebra (E i)]

theorem OAI.MainGap.lp_nonneg_iff (d : lp E ∞) : 0 ≤ d ↔ ∀ i, 0 ≤ d i := by sorry
