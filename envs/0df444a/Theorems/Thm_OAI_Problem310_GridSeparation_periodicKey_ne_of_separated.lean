-- Prove2me | Theorems.Thm_OAI_Problem310_GridSeparation_periodicKey_ne_of_separated
-- name    : OAI.Problem310.GridSeparation.periodicKey_ne_of_separated
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:10:06.145986+00:00
-- url     : https://prove2.me/theorems/f2ea3d6d-3745-4c88-9fe4-9d526077a889
-- title:
--   Points a full mesh apart in both circular directions have different periodic grid keys
-- statement:
--   For real numbers $q$ and $x$ let $\{x\}=x-\lfloor x\rfloor\in[0,1)$ denote the fractional part of $x$, and define the periodic key
--   $$\kappa_q(x)=\bigl\lfloor q\,\{x\}\bigr\rfloor\in\mathbb{Z}.$$
--   When $q$ is a positive integer, $\kappa_q(x)\in\{0,\dots,q-1\}$ is the index $k$ of the cell $[k/q,(k+1)/q)$ of the grid of mesh $1/q$ on the circle $\mathbb{R}/\mathbb{Z}$ that contains $x$ modulo $1$.
--
--   **Theorem.** Let $q>0$ and let $x,y\in\mathbb{R}$ satisfy
--
--   $$1\le q\,(y-x)\le q-1 .$$
--
--   Then $\kappa_q(x)\ne\kappa_q(y)$.
--
--   After division by $q$ the hypothesis reads $\frac1q\le y-x\le1-\frac1q$: the point $y$ lies at least one mesh width $1/q$ to the right of $x$, and $x+1$ lies at least one mesh width to the right of $y$. So the two points are a full cell apart in both directions around the circle, and then they cannot have the same key, even when one of them lies on a cell boundary. The hypotheses can only be satisfied when $q\ge2$, and $q$ need not be an integer. The result is the separation fact that lets well-separated points of the circle be sent to different entries of a periodic lookup table.
--
--   **Formalization Note** The key is `periodicKey q x`, defined as `Int.floor (q * Int.fract x)`; Lean's `Int.fract x` is $x-\lfloor x\rfloor$, which lies in $[0,1)$ also for negative $x$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GridSeparation.lean#L18-L43

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation

open OAI OAI.Problem310 OAI.Problem310.GridSeparation
universe u_α

theorem OAI.Problem310.GridSeparation.periodicKey_ne_of_separated {q x y : ℝ} (hq : 0 < q)
    (hlo : 1 ≤ q * (y - x)) (hhi : q * (y - x) ≤ q - 1) :
    periodicKey q x ≠ periodicKey q y := by sorry
