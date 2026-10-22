-- Prove2me | Theorems.Thm_FullFormalization_Ival_nonneg
-- name    : FullFormalization.Ival_nonneg
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:55:24.905147+00:00
-- url     : https://prove2.me/theorems/cf921212-d406-4038-8b89-c9c26300a8c5
-- title:
--   Nonnegativity of the smooth-convex interpolation residual $I_{ij}$
-- statement:
--   For a convex differentiable function $f$ on a real inner product space whose gradient is globally $1$-Lipschitz, the smooth-convex interpolation residual evaluated at two points $x$ and $y$ is nonnegative:
--   $$I_{ij} \;=\; f(x) - f(y) - \langle \nabla f(y),\, x - y\rangle - \tfrac12\,\lVert \nabla f(x) - \nabla f(y)\rVert^{2} \;\ge\; 0 .$$
--   Here $f$ is the objective, $x$ and $y$ are the two evaluation points, $\nabla f$ is its gradient, and the two subtracted terms are the first-order Taylor correction at $y$ followed by the smoothness penalty. This is Lemma 2.1 of the manuscript (2.2), the single analytic ingredient of the NAG upper-bound certificate; the source proves it rather than postulating it.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §2, Lemma 2.1, eq. (2.2); Lean: FullFormalization.SmoothConvex lines 219-249

-- Generated from F:/20261008/FullFormalization\FullFormalization\SmoothConvex.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.SmoothConvex

  Source section 2: the smooth-convex interpolation residual

      I_{ij} = F_i - F_j - ⟨g_j, x_i - x_j⟩ - (1/2) ‖g_i - g_j‖²  ≥ 0   (2.2)

  and its proof, which the source carries out in full (lines 211-279) rather
  than citing.  Nothing here is an axiom: (2.2) is derived from convexity and
  global 1-Lipschitzness of the gradient, through exactly the two ingredients
  the source uses.

  Source argument (lines 213-277):
    * `φ = f - ⟪g_j, ·⟫` is convex and 1-smooth, and `∇φ(x_j) = 0`, so `x_j`
      minimises `φ`;
    * the descent lemma gives `φ(x_i - ∇φ(x_i)) ≤ φ(x_i) - ½‖∇φ(x_i)‖²`;
    * hence `φ(x_i) - φ(x_j) ≥ ½‖∇φ(x_i)‖²`, which is (2.2).

  The two ingredients are proved here from scratch:

  * `descent_lemma` — for a differentiable `ψ` whose gradient is globally
    1-Lipschitz, `ψ (u - ∇ψ u) ≤ ψ u - ½‖∇ψ u‖²`.  No convexity is used.
    This is the source's `descent lemma` (quoted at line 227).

  * `convexOn_le_gradient` — for convex differentiable `f`,
    `f y ≥ f x + ⟪∇f x, y - x⟫`, which is what makes a zero gradient a global
    minimiser (source line 235: "hence `x_j` is the global minimiser of `φ`").

  Both reduce to one-dimensional calculus along a segment, using Mathlib's
  `ConvexOn.deriv_le_slope` (convexity versus secant slope) and
  `antitoneOn_of_hasDerivWithinAt_nonpos` (a nonpositive derivative makes a
  function antitone), the formal counterpart of integrating the derivative
  bound.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Theorems.Thm_FullFormalization_convexOn_le_gradient
import Theorems.Thm_FullFormalization_descent_lemma
import Theorems.Thm_FullFormalization_differentiable_inner_const
import Theorems.Thm_FullFormalization_gradient_inner_const
import Theorems.Thm_FullFormalization_gradient_sub
import Theorems.Thm_FullFormalization_gradient_sub_inner

open scoped Gradient RealInnerProductSpace
open Set

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Gradient of a difference, and of `⟪c, ·⟫` -/









/-! ### The first-order condition for convex differentiable functions -/



/-! ### The descent lemma for a 1-smooth function (source line 227) -/



/-! ### Lemma 2.1 -/



end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
open Set
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem FullFormalization.Ival_nonneg {f : E → ℝ} (hconv : ConvexOn ℝ Set.univ f)
    (hd : Differentiable ℝ f) (hsm : ∀ a b : E, ‖∇ f a - ∇ f b‖ ≤ ‖a - b‖) (x y : E) :
    0 ≤ Ival (f x) (f y) x y (∇ f x) (∇ f y) := by sorry
