-- Prove2me | Theorems.Thm_OAI_MainGap_compression_of_conditional_loss
-- name    : OAI.MainGap.compression_of_conditional_loss
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:36:40.358454+00:00
-- url     : https://prove2.me/theorems/aa63ea46-fb6e-4ee5-98f7-f0d5c850a43d
-- title:
--   A loss bound $\|pck\|\le r\|k\|$ on $\mathrm{Her}(q)$ gives compression constant $r/\tau$ above level $\tau$ of $p$
-- statement:
--   Let $A$ be a unital C*-algebra, ordered by its cone of positive elements. For $h\in A$ let $\mathrm{Her}(h)=\overline{\{hah^*: a\in A\}}$. For $\tau>0$ let
--   $$
--   \varphi_\tau(t)=\min\Big\{1,\ \frac{\max(t-\tau,0)}{1-\tau}\Big\}
--   $$
--   be the ramp that vanishes for $t\le\tau$ and (when $\tau<1$) rises linearly to $1$ at $t=1$; for positive $p$ let $\varphi_\tau(p)$ be given by functional calculus.
--
--   Let $p,q,c\in A$ with $p\ge0$, and let $\tau>0$ and $r\ge0$. Assume that $\|p\,c\,k\|\le r\,\|k\|$ for every $k\in\mathrm{Her}(q)$. Then
--   $$
--   \|x\,c\,k\|\ \le\ \frac r\tau\,\|x\|\,\|k\|\qquad\text{for all }x\in\mathrm{Her}(\varphi_\tau(p))\text{ and }k\in\mathrm{Her}(q).
--   $$
--   In other words, the pair of hereditary subalgebras $\mathrm{Her}(\varphi_\tau(p))$ and $\mathrm{Her}(q)$ is compressed by $c$ with constant $r/\tau$.
--
--   The lemma turns a one-sided loss estimate for the single element $pc$ into a two-sided compression estimate for the whole hereditary subalgebra of the part of $p$ above level $\tau$. Choosing $r<\tau<1$ gives a compression constant strictly less than $1$, which is what the shrinking step needs.
--
--   **Formalization Note** The conclusion is `HerCompression (ramp p τ 1) q c (r/τ)`, where `HerCompression e q c κ` means $\|xck\|\le\kappa\|x\|\|k\|$ for $x\in\mathrm{Her}(e)$ and $k\in\mathrm{Her}(q)$. For $\tau\ge1$ the formula for $\varphi_\tau$ is read with Lean's conventions (division by zero gives $0$), and the statement remains valid; in applications $0<\tau<1$. The hypothesis $r\ge0$ is part of the statement but is not used in the proof.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Compression.lean#L244-L265

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
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem OAI.MainGap.compression_of_conditional_loss {p q c : A} (hp : 0 ≤ p) {τ r : ℝ}
    (hτ : 0 < τ) (_hr : 0 ≤ r)
    (h : ∀ k : A, k ∈ Her q → ‖p*c*k‖ ≤ r*‖k‖) :
    HerCompression (ramp p τ 1) q c (r/τ) := by sorry
