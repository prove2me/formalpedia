-- Prove2me | Theorems.Thm_OAI_MainGap_cutInverseFn_bound
-- name    : OAI.MainGap.cutInverseFn_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:32:16.47381+00:00
-- url     : https://prove2.me/theorems/4a07a909-4a22-49d9-9e81-c75b4803ec53
-- title:
--   The cut-off inverse $t/\max(\delta,t)^2$ lies between $0$ and $1/\delta$
-- statement:
--   For a real number $\delta>0$ define the *cut-off inverse function*
--   $$
--   g_\delta(t)=\frac{t}{\max(\delta,t)^2},
--   $$
--   so that $g_\delta(t)=t/\delta^2$ for $t\le\delta$ and $g_\delta(t)=1/t$ for $t\ge\delta$. Then for every real $t\ge0$,
--   $$
--   0\ \le\ g_\delta(t)\ \le\ \frac1\delta .
--   $$
--
--   Applied by continuous functional calculus to a positive element $a$ of a C*-algebra, $g_\delta(a)$ is a bounded partial inverse of $a$: $a\,g_\delta(a)$ acts as the identity on the hereditary subalgebra of the cut-down $(a-\delta)_+$. The lemma shows that this partial inverse is positive and has norm at most $1/\delta$, which controls the constants in the compression estimates.
--
--   **Formalization Note** The function is `cutInverseFn δ t`. The Lean statement sits in a section that declares a C*-algebra variable, but that variable does not occur in it: this is a purely real-variable inequality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Compression.lean#L22-L38

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

theorem OAI.MainGap.cutInverseFn_bound {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    0 ≤ cutInverseFn δ t ∧ cutInverseFn δ t ≤ 1/δ := by sorry
