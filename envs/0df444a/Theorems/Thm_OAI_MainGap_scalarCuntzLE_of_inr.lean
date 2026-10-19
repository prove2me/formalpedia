-- Prove2me | Theorems.Thm_OAI_MainGap_scalarCuntzLE_of_inr
-- name    : OAI.MainGap.scalarCuntzLE_of_inr
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:53:36.595348+00:00
-- url     : https://prove2.me/theorems/3e5c73da-1381-4ec8-8ca5-30e704f60f56
-- title:
--   Cuntz comparison in the unitization descends to the algebra
-- statement:
--   Let $A$ be a C*-algebra, not necessarily unital, with its usual order, and let $\tilde A=\mathbb{C}\oplus A$ be its unitization, in which $x\in A$ is identified with $(0,x)$. In a C*-algebra $B$ write $u\precsim_B v$ if $u\in\overline{\{\,w^*\,v\,w:\ w\in B\,\}}$. Let $u,v\in A$ with $v\ge0$. Then
--   $$u\precsim_{\tilde A}v\ \Longrightarrow\ u\precsim_A v,$$
--   that is, if $u$ is a limit of elements $w^*vw$ with $w\in\tilde A$, then it is also a limit of such elements with $w\in A$. No positivity is assumed on $u$.
--
--   This allows comparisons obtained in the unitization, for instance by results that need a unit, to be transferred back to the original non-unital algebra.
--
--   **Formalization Note** The hypothesis is `ScalarCuntzLE (Unitization.inr u) (Unitization.inr v)` in `Unitization ℂ A`, and the conclusion is `ScalarCuntzLE u v` in $A$. The order is `CStarAlgebra.spectralOrder`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/IdealComparison.lean#L117-L158

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
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealComparison

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.idealComparisonNonUnitalPartialOrder
attribute [local instance] OAI.MainGap.idealComparisonNonUnitalStarOrderedRing
variable {A : Type*} [NonUnitalCStarAlgebra A]

theorem OAI.MainGap.scalarCuntzLE_of_inr {u v : A} (hv : 0 ≤ v)
    (h : ScalarCuntzLE (Unitization.inr u : Unitization ℂ A) (Unitization.inr v)) :
    ScalarCuntzLE u v := by sorry
