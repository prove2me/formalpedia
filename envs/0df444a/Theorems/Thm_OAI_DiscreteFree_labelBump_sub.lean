-- Prove2me | Theorems.Thm_OAI_DiscreteFree_labelBump_sub
-- name    : OAI.DiscreteFree.labelBump_sub
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T10:02:04.547934+00:00
-- url     : https://prove2.me/theorems/98396ee7-e6d5-4180-9bc7-cd3d52a1fe14
-- title:
--   Lipschitz bound for a truncated cone bump pulled back by a $1$-Lipschitz map
-- statement:
--   Let $M$ and $N$ be metric spaces, let $h:M\to N$ be $1$-Lipschitz, let $a\in N$, and let $L\ge0$ and $K>0$ be real numbers. The *label bump* of height $L$ and radius $K$ around $a$ is the function
--   $$b(t)=L\cdot\max\Bigl(1-\frac{d\bigl(a,h(t)\bigr)}{K},\ 0\Bigr),\qquad t\in M .$$
--
--   **Theorem.** For all $x,y\in M$,
--   $$
--   |b(x)-b(y)|\le\frac{L}{K}\,d(x,y).
--   $$
--
--   The bump takes values in $[0,L]$, equals $L$ at every $t$ with $h(t)=a$, and is positive only where $d(a,h(t))<K$. By the theorem it is $1$-Lipschitz as soon as $L\le K$. In the construction of test functions on a metric block, $h$ is the map sending a point to its label, and the bump is a Lipschitz substitute for the indicator of the points whose labels are close to $a$.
--
--   **Formalization Note** The bump is `labelBump h a L K`, and $h$ is assumed `LipschitzWith 1 h`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/LabelBumps.lean#L35-L49

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

open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
open scoped BigOperators Classical
variable {M N : Type*} [MetricSpace M] [MetricSpace N]

theorem OAI.DiscreteFree.labelBump_sub (h : M → N) (hh : LipschitzWith 1 h) (a : N)
    {L K : ℝ} (hL : 0 ≤ L) (hK : 0 < K) (x y : M) :
    |labelBump h a L K x - labelBump h a L K y| ≤ (L/K) * dist x y := by sorry
