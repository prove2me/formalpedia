-- Prove2me | Theorems.Thm_OAI_MainGap_scalarCuntzLE_iff_finite
-- name    : OAI.MainGap.scalarCuntzLE_iff_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:47:30.551269+00:00
-- url     : https://prove2.me/theorems/08d1b90b-016f-4c19-b455-8bf5534f3750
-- title:
--   Scalar Cuntz comparison agrees with comparison of $1\times1$ matrices
-- statement:
--   Let $A$ be a C*-algebra, not necessarily unital. For $u,v\in A$ write $u\precsim v$ (scalar Cuntz comparison) if
--   $$u\in\overline{\{\,w^*\,v\,w:\ w\in A\,\}}.$$
--   For matrices $d\in M_n(A)$ and $v\in M_m(A)$ write $d\precsim v$ if there is a sequence of rectangular matrices $r_j\in M_{m\times n}(A)$ with $r_j^*\,v\,r_j\to d$ in the C*-algebra $M_n(A)$. Then for all $u,v\in A$, with $(u),(v)\in M_1(A)$ the corresponding $1\times1$ matrices,
--   $$u\precsim v\quad\Longleftrightarrow\quad (u)\precsim(v).$$
--   No positivity is assumed.
--
--   The scalar form is convenient for closure arguments in $A$, while the matrix form is the setting in which block sums and proper infiniteness are expressed; this equivalence moves statements between the two. For example, transitivity of the scalar relation follows from transitivity of the matrix relation.
--
--   **Formalization Note** The scalar relation is `ScalarCuntzLE u v`, the matrix relation is `FiniteCuntzLE` on `CStarMatrix`, and $(u)$ is `scalarCorner u`. A spectral-order instance on $A$ is in scope but plays no role.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/IdealDetection.lean#L124-L145

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
attribute [local instance] OAI.MainGap.idealDetectionOrder
attribute [local instance] OAI.MainGap.idealDetectionStarOrder
variable {A : Type*} [NonUnitalCStarAlgebra A]

theorem OAI.MainGap.scalarCuntzLE_iff_finite (u v : A) :
    ScalarCuntzLE u v ↔ FiniteCuntzLE (scalarCorner u) (scalarCorner v) := by sorry
