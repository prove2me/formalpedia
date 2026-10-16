-- Prove2me | Theorems.Thm_OAI_DiscreteFree_MetricWedge_separated
-- name    : OAI.DiscreteFree.MetricWedge.separated
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T10:15:32.030025+00:00
-- url     : https://prove2.me/theorems/0fb93763-9da8-4944-8a21-844a0cd25929
-- title:
--   A wedge of $1$-separated pointed metric spaces is $1$-separated
-- statement:
--   Let $(M_n,d_n)_{n\in\mathbb N}$ be a sequence of metric spaces with base points $o_n\in M_n$. Their *metric wedge* $W=\bigvee_n(M_n,o_n)$ glues all base points into a single point $\ast$. As a set, $W=\{\ast\}\sqcup\bigsqcup_n(M_n\setminus\{o_n\})$, where $(n,x)$ denotes the copy of $x\in M_n\setminus\{o_n\}$. The metric is
--
--   $$
--   d(\ast,(n,x))=d_n(x,o_n),\qquad d((n,x),(n,y))=d_n(x,y),\qquad d((n,x),(m,y))=d_n(x,o_n)+d_m(y,o_m)\quad(n\ne m).
--   $$
--
--   **Theorem.** Suppose every $M_n$ is $1$-separated, i.e. $d_n(x,y)\ge1$ whenever $x\ne y$ in $M_n$. Then the wedge $W$ is $1$-separated:
--
--   $$
--   \forall\,\xi,\eta\in W:\qquad \xi\ne\eta\ \Longrightarrow\ d(\xi,\eta)\ge1 .
--   $$
--
--   Uniform separation is the standing hypothesis under which point masses in Lipschitz-free spaces have bounded coordinate functionals. This lemma shows that the hypothesis survives the gluing of countably many pointed spaces at their base points. That gluing is how the metric blocks are assembled into a single countable, uniformly discrete metric space.
--
--   **Formalization Note** The wedge is `MetricWedge.Point M o`, implemented as `Option (Σ n, {x : M n // x ≠ o n})`, with `none` playing the role of $\ast$. All $M_n$ live in a common universe.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/RetainedWedge.lean#L18-L32

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

theorem OAI.DiscreteFree.MetricWedge.separated (sep : ∀ n (x y : M n), x ≠ y → 1 ≤ dist x y)
    (x y : Point M o) (hxy : x ≠ y) : 1 ≤ dist x y := by sorry
