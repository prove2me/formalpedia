-- Prove2me | Theorems.Thm_OAI_MainGap_scalarCuntzLE_of_mem_Her
-- name    : OAI.MainGap.scalarCuntzLE_of_mem_Her
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:51:21.759632+00:00
-- url     : https://prove2.me/theorems/6513afc9-c717-4420-92fe-e74acdc8bb3a
-- title:
--   Positive elements of the hereditary subalgebra of $v$ are Cuntz-below $v$
-- statement:
--   Let $A$ be a C*-algebra, not necessarily unital, with its usual order. For $v\in A$ let $\operatorname{Her}(v)=\overline{\{\,v\,b\,v^*:\ b\in A\,\}}$, and for $u,v\in A$ write $u\precsim v$ if $u\in\overline{\{\,w^*\,v\,w:\ w\in A\,\}}$. Let $u,v\in A$ with $u\ge0$ and $v\ge0$. Then
--   $$u\in\operatorname{Her}(v)\ \Longrightarrow\ u\precsim v.$$
--
--   This is the basic source of Cuntz comparisons: membership in the hereditary subalgebra of $v$ implies domination by $v$. Combined with the fact that $0\le u\le v$ implies $u\in\operatorname{Her}(v)$, it shows that order domination implies Cuntz domination, and it also gives $Kv\precsim v$ for every $K>0$.
--
--   **Formalization Note** The relation is `ScalarCuntzLE u v`, $\operatorname{Her}(v)$ is `Her v`, and the order is `CStarAlgebra.spectralOrder`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/IdealDetection.lean#L157-L178

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

theorem OAI.MainGap.scalarCuntzLE_of_mem_Her {u v : A} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : u ∈ Her v) : ScalarCuntzLE u v := by sorry
