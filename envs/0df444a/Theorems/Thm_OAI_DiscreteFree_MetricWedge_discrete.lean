-- Prove2me | Theorems.Thm_OAI_DiscreteFree_MetricWedge_discrete
-- name    : OAI.DiscreteFree.MetricWedge.discrete
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T10:17:09.408174+00:00
-- url     : https://prove2.me/theorems/3678e408-1e67-420a-9663-e95d87a7f0f5
-- title:
--   A wedge of $1$-separated pointed metric spaces is topologically discrete
-- statement:
--   Let $(M_n,d_n)_{n\in\mathbb N}$ be a sequence of metric spaces with base points $o_n\in M_n$. Their *metric wedge* $W=\bigvee_n(M_n,o_n)$ glues all base points into a single point $\ast$. As a set, $W=\{\ast\}\sqcup\bigsqcup_n(M_n\setminus\{o_n\})$, where $(n,x)$ denotes the copy of $x\in M_n\setminus\{o_n\}$. The metric is
--
--   $$
--   d(\ast,(n,x))=d_n(x,o_n),\qquad d((n,x),(n,y))=d_n(x,y),\qquad d((n,x),(m,y))=d_n(x,o_n)+d_m(y,o_m)\quad(n\ne m).
--   $$
--
--   **Theorem.** Suppose every $M_n$ is $1$-separated, i.e. $d_n(x,y)\ge1$ whenever $x\ne y$ in $M_n$. Then the metric topology of the wedge $W$ is discrete: every subset of $W$ is open, or equivalently
--
--   $$
--   \{\xi\}\ \text{is open in } W\quad\text{for every } \xi\in W .
--   $$
--
--   Discreteness matters for the main construction. In a discrete space every compact set is finite. So once a closed ball of the wedge contains infinitely many points, the wedge cannot be proper, i.e. closed balls cannot all be compact.
--
--   **Formalization Note** The wedge is `MetricWedge.Point M o`, an `Option` of a sigma type of the punctured spaces, and the conclusion is the typeclass `DiscreteTopology (Point M o)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/RetainedWedge.lean#L34-L49

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

open OAI OAI.DiscreteFree OAI.DiscreteFree.MetricWedge
open scoped BigOperators ENNReal
open scoped Classical BigOperators
universe u
variable (M : ℕ → Type u) [∀ n, MetricSpace (M n)] (o : ∀ n, M n)

theorem OAI.DiscreteFree.MetricWedge.discrete (sep : ∀ n (x y : M n), x ≠ y → 1 ≤ dist x y) :
    DiscreteTopology (Point M o) := by sorry
