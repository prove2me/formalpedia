-- Prove2me | Theorems.Thm_OAI_DiscreteFree_MetricWedge_hasAP
-- name    : OAI.DiscreteFree.MetricWedge.hasAP
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T10:22:04.768898+00:00
-- url     : https://prove2.me/theorems/c3bfec24-c301-47d6-bea4-fd9348a920e8
-- title:
--   The free space of a wedge of bounded $1$-separated spaces has the approximation property
-- statement:
--   For a pointed metric space $(M,o)$, $\mathrm{Lip}_0(M)$ is the space of real Lipschitz functions on $M$ that vanish at $o$, normed by the best Lipschitz constant. The *Lipschitz-free space* $\mathcal F(M)$ is the closed linear span of the point evaluations $\delta_x\colon f\mapsto f(x)$, $x\in M$, in the dual space $\mathrm{Lip}_0(M)^*$.
--
--   A real normed space $X$ has the *approximation property* (AP) in the following compact-uniform sense. For every compact set $C\subseteq X$ and every $\varepsilon>0$, there are a bounded linear operator $T\colon X\to X$ with finite-dimensional range and a number $\eta<\varepsilon$ such that $\|Tu-u\|\le\eta$ for all $u\in C$. No bound on $\|T\|$ is required.
--
--   Let $(M_n,d_n)_{n\in\mathbb N}$ be a sequence of metric spaces with base points $o_n\in M_n$. Their *metric wedge* $W=\bigvee_n(M_n,o_n)$ glues all base points into a single point $\ast$. As a set, $W=\{\ast\}\sqcup\bigsqcup_n(M_n\setminus\{o_n\})$, where $(n,x)$ denotes the copy of $x\in M_n\setminus\{o_n\}$. The metric is
--
--   $$
--   d(\ast,(n,x))=d_n(x,o_n),\qquad d((n,x),(n,y))=d_n(x,y),\qquad d((n,x),(m,y))=d_n(x,o_n)+d_m(y,o_m)\quad(n\ne m).
--   $$
--
--   **Theorem.** Assume that every $M_n$ is $1$-separated, i.e. $d_n(x,y)\ge1$ for $x\ne y$. Assume also that each $M_n$ is bounded around its base point: there are numbers $B_n\ge0$ with $d_n(x,o_n)\le B_n$ for all $n$ and all $x\in M_n$. Then the Lipschitz-free space of the wedge, with base point $\ast$, has the approximation property:
--
--   $$
--   \mathcal F\Bigl(\bigvee_{n\in\mathbb N}(M_n,o_n)\Bigr)\ \text{has the AP.}
--   $$
--
--   The radii $B_n$ need not be uniformly bounded, so the wedge itself may be unbounded. This is the positive half of the main counterexample. There the components are metric blocks whose free spaces have the bounded approximation property only with constants that grow without bound, and this theorem still yields the AP for the free space of their wedge.
--
--   **Formalization Note** The wedge is `MetricWedge.Point M o` with base point `MetricWedge.base M o`. `HasAP X` is the compact-uniform formulation above, with an explicit $\eta<\varepsilon$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/WedgeApproximation.lean#L156-L177

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

open OAI OAI.DiscreteFree OAI.DiscreteFree.MetricWedge
open scoped BigOperators ENNReal
open scoped Classical BigOperators
universe u
variable (M : ℕ → Type u) [∀ n, MetricSpace (M n)] (o : ∀ n, M n)

theorem OAI.DiscreteFree.MetricWedge.hasAP (sep : ∀ n (x y : M n), x ≠ y → 1 ≤ dist x y)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (hb : ∀ n (x : M n), dist x (o n) ≤ B n) :
    HasAP (FreeSpace (base M o)) := by sorry
