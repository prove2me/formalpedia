-- Prove2me | Theorems.Thm_OAI_MainGap_cut_sqrt_lower
-- name    : OAI.MainGap.cut_sqrt_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:33:06.22953+00:00
-- url     : https://prove2.me/theorems/a00014c8-3ca7-4488-88bf-6cc648be4339
-- title:
--   Lower bound $\delta\,(d-\delta)_+\le(d-\delta)_+^{1/2}\,d\,(d-\delta)_+^{1/2}$ for positive $d$
-- statement:
--   Let $A$ be a C*-algebra, not necessarily unital, ordered by its cone of positive elements. Let $d\in A$ be positive and let $\delta\ge0$. Let $(d-\delta)_+=f(d)$ be the cut-down of $d$ defined by continuous functional calculus with $f(t)=\max(t-\delta,0)$, and let $(d-\delta)_+^{1/2}$ be its positive square root. Then
--   $$
--   \delta\,(d-\delta)_+\ \le\ (d-\delta)_+^{1/2}\;d\;(d-\delta)_+^{1/2}.
--   $$
--
--   The cut-down $(d-\delta)_+$ is supported on the part of the spectrum of $d$ above $\delta$, so compressing $d$ by its square root yields at least $\delta$ times the cut-down. The inequality shows that a defect element $d$ is large, in operator order, on the hereditary subalgebra of its own cut-down. It drives both the norm-loss estimate and the vanishing criterion of the conditional compression argument.
--
--   **Formalization Note** The algebra carries an arbitrary partial order making it a star-ordered ring, which for a C*-algebra is the usual order. The cut-down is `cut d δ` and the square root is `CFC.sqrt`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Compression.lean#L82-L104

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

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem OAI.MainGap.cut_sqrt_lower {d : A} (hd : 0 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ) :
    δ • cut d δ ≤ CFC.sqrt (cut d δ) * d * CFC.sqrt (cut d δ) := by sorry
