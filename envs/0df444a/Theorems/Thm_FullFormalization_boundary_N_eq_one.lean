-- Prove2me | Theorems.Thm_FullFormalization_boundary_N_eq_one
-- name    : FullFormalization.boundary_N_eq_one
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:35:01.734018+00:00
-- url     : https://prove2.me/theorems/5b6ee418-487c-4cdf-bfb0-66f653ef5316
-- title:
--   The exact $N=1$ certificate, as three residuals plus two squares
-- statement:
--   Let $E$ be a real inner product space, let $r, x_1, g_0, g_1 \in E$ with $x_1 = r - g_0$, and let $F_0, F_1 \in \mathbb{R}$. Then the boundary defect admits the exact decomposition
--   $$\frac{\|r\|^2}{6} - F_1 = \frac12\bigl(I_{\star,0} + I_{0,1} + I_{\star,1}\bigr) + \frac38\left\|g_0 - \frac{r}{3}\right\|^2 + \frac12\left\|g_1 - \frac{x_1}{2}\right\|^2 .$$
--   Here $r$ is the starting point, $x_1 = r - g_0$ is the first Nesterov output (equal to the first gradient step because the first momentum coefficient is $m_0 = 0$), $g_0$ and $g_1$ are the two gradients, and $F_0, F_1$ the two function values at them; the quantity $I_{i,j} = F_i - F_j - \langle g_j, x_i - x_j\rangle - \tfrac12\|g_i - g_j\|^2$ is the smooth-convex interpolation residual of source (2.1), and $I_{\star,j}$ denotes its specialisation to the minimiser.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §18, eq. (18.1); Lean: FullFormalization.NAGUpperBound lines 37-52

-- Generated from F:/20261008/FullFormalization\FullFormalization\NAGUpperBound.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.NAGUpperBound

  Source section 18: the dedicated exact certificate for the boundary case `N = 1`.

  Source (18.1):

      ‖r‖²/6 - F_1 = (1/2)(I_{⋆,0} + I_{0,1} + I_{⋆,1})
                     + (3/8) ‖g_0 - r/3‖² + (1/2) ‖g_1 - x_1/2‖²

  and the resulting bound `F_1 ≤ ‖r‖²/6`, which agrees with
  `2/(1² + 7·1 + 4) = 1/6`, so that the all-`N` formula has no gap at `N = 1`.

  The general `N ≥ 2` chain certificate does *not* cover `N = 1` (its index
  ranges are empty), which is exactly why the source gives this case
  separately.

  **Scalar-multiplication pitfall.**  In Lean a bare `(1 / 3) • r` elaborates
  the numeral `1 / 3` at type `ℕ` (where it is `0`), silently turning the term
  into `0 • r`.  Every scalar below is therefore written with an explicit `ℝ`
  ascription, e.g. `((1 : ℝ) / 3) • r`.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_NAGUpperBound
import Definitions.Def_RationalNAG

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]







end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem FullFormalization.boundary_N_eq_one (r x1 g0 g1 : E) (F0 F1 : ℝ) (hx1 : x1 = r - g0) :
    ‖r‖ ^ 2 / 6 - F1
      = (1 / 2) * (Ival 0 F0 0 r 0 g0 + Ival F0 F1 r x1 g0 g1 + Ival 0 F1 0 x1 0 g1)
        + (3 / 8) * ‖g0 - ((1 : ℝ) / 3) • r‖ ^ 2
        + (1 / 2) * ‖g1 - ((1 : ℝ) / 2) • x1‖ ^ 2 := by sorry
