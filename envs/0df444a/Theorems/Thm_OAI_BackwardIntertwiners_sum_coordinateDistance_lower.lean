-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_sum_coordinateDistance_lower
-- name    : OAI.BackwardIntertwiners.sum_coordinateDistance_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:33:11.446975+00:00
-- url     : https://prove2.me/theorems/a7fe6d39-7eae-423b-b3f6-0c96fe4a78f8
-- title:
--   Sums of $\max(j+1,-j)$ over $n$ consecutive integers are at least $\lfloor (n+1)^2/4\rfloor$
-- statement:
--   For $j\in\mathbb{Z}$ let
--   $$d(j)=\max(j+1,\,-j),$$
--   so that $d(j)=j+1$ for $j\ge0$ and $d(j)=-j$ for $j<0$; in particular $d(j)\ge1$. For $n\in\mathbb{N}$ let $p(n)=\lfloor (n+1)^2/4\rfloor$ (integer division).
--
--   **Theorem.** For every $n\in\mathbb{N}$ and every $j\in\mathbb{Z}$,
--   $$\Bigl\lfloor\frac{(n+1)^2}{4}\Bigr\rfloor\;\le\;\sum_{r=0}^{n-1}d(j+r).$$
--   For $n=0$ both sides are $0$.
--
--   The theorem bounds from below the sum of $d$ over any window of $n$ consecutive integers, uniformly in the position $j$ of the window. In the construction, the exponent of the forward weighted shift at position $j$ is at least $10\,d(j)$, so any product of $n$ consecutive shift weights is at most $e^{-10\lfloor(n+1)^2/4\rfloor}$; this gives the norm bound for the $n$-th power of the forward shift that makes it quasinilpotent.
--
--   **Formalization Note** In Lean, $d$ is `coordinateDistance j = max (j+1) (-j)` with values in `ℤ`, and $p$ is `powerCost n = (n+1)^2/4`, computed with natural-number division and then cast to `ℤ`; the sum runs over `Finset.range n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/FiberMaps.lean#L32-L56

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_HaarBase
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberMaps

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology
open Topology MeasureTheory Set
open scoped ENNReal

theorem OAI.BackwardIntertwiners.sum_coordinateDistance_lower (n : ℕ) (j : ℤ) :
    (powerCost n : ℤ) ≤ ∑ r ∈ Finset.range n, coordinateDistance (j+(r:ℤ)) := by sorry
