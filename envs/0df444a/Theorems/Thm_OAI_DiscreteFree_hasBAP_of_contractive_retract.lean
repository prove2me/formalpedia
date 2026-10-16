-- Prove2me | Theorems.Thm_OAI_DiscreteFree_hasBAP_of_contractive_retract
-- name    : OAI.DiscreteFree.hasBAP_of_contractive_retract
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T10:19:09.001054+00:00
-- url     : https://prove2.me/theorems/d75ac89e-6bbd-41aa-9e33-9022d620d220
-- title:
--   The bounded approximation property with constant $\Lambda$ passes to contractive retracts
-- statement:
--   Let $X$ be a real normed space and $\Lambda\in\mathbb R$. Say that $X$ has the *$\Lambda$-bounded approximation property* ($\Lambda$-BAP) if the following holds. For every compact set $C\subseteq X$ and every $\varepsilon>0$, there are a bounded linear operator $T\colon X\to X$ of finite rank (its range is finite-dimensional) with $\|T\|\le\Lambda$, and a number $\eta<\varepsilon$, such that $\|Tu-u\|\le\eta$ for all $u\in C$.
--
--   **Theorem.** Let $E$ and $F$ be real normed spaces, and let $I\colon E\to F$ and $P\colon F\to E$ be bounded linear operators with
--
--   $$
--   \|I\|\le1,\qquad \|P\|\le1,\qquad P\circ I=\mathrm{id}_E .
--   $$
--
--   If $F$ has the $\Lambda$-BAP for some $\Lambda\in\mathbb R$, then $E$ has the $\Lambda$-BAP with the same constant $\Lambda$.
--
--   Under these hypotheses, $I$ is automatically an isometric embedding and $IP$ is a norm-one projection of $F$ onto $I(E)$. The theorem therefore says that the BAP constant does not increase when passing to a $1$-complemented subspace. In the main construction it transfers a bounded approximation property from the free space of a wedge of metric spaces to the free space of each component. As a result, a component that fails the $\Lambda$-BAP rules out the $\Lambda$-BAP for the whole wedge.
--
--   **Formalization Note** `HasBAP X Λ` is the compact-uniform formulation above, phrased with an explicit $\eta<\varepsilon$. Completeness of $E$ and $F$ is not assumed, and $\Lambda$ is an arbitrary real number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/WedgeApproximation.lean#L37-L56

import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring
import Definitions.Def_OAI_Analysis_LipschitzFree_BlockObstruction
import Definitions.Def_OAI_Analysis_LipschitzFree_Functor
import Definitions.Def_OAI_Analysis_LipschitzFree_Wedge
import Definitions.Def_OAI_Analysis_LipschitzFree_RetainedWedge
import Definitions.Def_OAI_Analysis_LipschitzFree_WedgeApproximation

open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
open scoped Classical BigOperators
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem OAI.DiscreteFree.hasBAP_of_contractive_retract (I : E →L[ℝ] F) (P : F →L[ℝ] E)
    (hI : ‖I‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hPI : P.comp I = ContinuousLinearMap.id ℝ E)
    (Λ : ℝ) (h : HasBAP F Λ) : HasBAP E Λ := by sorry
