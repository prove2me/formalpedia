-- Prove2me | Theorems.Thm_FullFormalization_boundary_bound
-- name    : FullFormalization.boundary_bound
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T06:01:52.576981+00:00
-- url     : https://prove2.me/theorems/52b925f3-c6ee-4346-b8ec-e58cbecd735b
-- title:
--   The $N=1$ upper bound: $f(x_1) - f(0) \le \|r\|^2/6$
-- statement:
--   Let $f : E \to \mathbb{R}$ be convex, differentiable and $1$-smooth, with $f(0) = 0$, $\nabla f(0) = 0$ and $0$ a global minimiser — the normalised setting in which the optimum has been translated to the origin and the smoothness constant scaled to $1$ — and let $r \in E$ be a starting point. Then the value at the first extrapolated Nesterov iterate obeys
--   $$f(x_1) - f(0) \;\le\; \frac{\|r\|^2}{6}, \qquad x_1 = r - \nabla f(r).$$
--   Here $x_1$ is the first iterate of the rational-momentum Nesterov method at $L = 1$, which equals a single gradient step because the first momentum coefficient is $m_0 = 0$, and $\|r\|^2/6$ is the value at $N = 1$ of the all-$N$ bound $2/(N^2+7N+4)$. The result closes the single boundary case the chain certificate leaves open, so that the all-$N$ formula has no gap at $N = 1$.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §18; Lean: FullFormalization.NAGUpperBound lines 64-87

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
import Theorems.Thm_FullFormalization_Ival_nonneg
import Theorems.Thm_FullFormalization_boundary_N_eq_one
import Theorems.Thm_FullFormalization_convexOn_le_gradient
import Theorems.Thm_FullFormalization_descent_lemma
import Theorems.Thm_FullFormalization_differentiable_inner_const
import Theorems.Thm_FullFormalization_gradient_inner_const
import Theorems.Thm_FullFormalization_gradient_sub
import Theorems.Thm_FullFormalization_gradient_sub_inner
import Theorems.Thm_FullFormalization_mom_zero
import Theorems.Thm_FullFormalization_nagX_succ
import Theorems.Thm_FullFormalization_nagX_zero
import Theorems.Thm_FullFormalization_nagY_succ
import Theorems.Thm_FullFormalization_nagY_succ_one
import Theorems.Thm_FullFormalization_nagY_zero

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

theorem FullFormalization.boundary_bound {f : E → ℝ} (hf : NormalizedAtZero f) (r : E) :
    f (nagX f 1 r 1) - f 0 ≤ ‖r‖ ^ 2 / 6 := by sorry
