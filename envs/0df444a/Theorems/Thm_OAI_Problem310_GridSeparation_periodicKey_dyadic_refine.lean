-- Prove2me | Theorems.Thm_OAI_Problem310_GridSeparation_periodicKey_dyadic_refine
-- name    : OAI.Problem310.GridSeparation.periodicKey_dyadic_refine
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:11:14.346155+00:00
-- url     : https://prove2.me/theorems/30ad05fe-0bc0-41f6-80c0-f16f44b6368d
-- title:
--   Nesting of periodic dyadic grids: the coarse key is the fine key divided by $2^{B-b}$
-- statement:
--   For a real number $q>0$ and $x\in\mathbb{R}$ let $\{x\}=x-\lfloor x\rfloor\in[0,1)$ be the fractional part of $x$ and
--   $$\kappa_q(x)=\bigl\lfloor q\,\{x\}\bigr\rfloor\in\mathbb{Z}$$
--   the *periodic key* of $x$ at mesh $1/q$, i.e. the index $k$ of the cell $[k/q,(k+1)/q)$ that contains $x$ modulo $1$.
--
--   Let $b\le B$ be natural numbers and $x\in\mathbb{R}$. Then the key at the coarse dyadic mesh $2^{-(b+2)}$ is obtained from the key at the fine mesh $2^{-(B+2)}$ by integer division by $2^{B-b}$:
--   $$\kappa_{2^{b+2}}(x)=\left\lfloor\frac{\kappa_{2^{B+2}}(x)}{2^{B-b}}\right\rfloor .$$
--
--   This is the nesting property of the periodic dyadic grids: every cell of mesh $2^{-(b+2)}$ is the union of $2^{B-b}$ consecutive cells of mesh $2^{-(B+2)}$, so the fine key determines every coarser key. It allows table addresses read at different dyadic resolutions to be compared, for instance to pass from a statement at one resolution to all coarser ones.
--
--   **Formalization Note** The right-hand side uses Lean's integer division `/` on $\mathbb{Z}$, which for a positive divisor is floor division; since the key is nonnegative this is ordinary division with remainder.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GridSeparation.lean#L151-L166

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation

open OAI OAI.Problem310 OAI.Problem310.GridSeparation
universe u_α

theorem OAI.Problem310.GridSeparation.periodicKey_dyadic_refine {b B : ℕ} (hb : b ≤ B) (x : ℝ) :
    periodicKey ((2 : ℝ) ^ (b + 2)) x =
      periodicKey ((2 : ℝ) ^ (B + 2)) x / (2 : ℤ) ^ (B - b) := by sorry
