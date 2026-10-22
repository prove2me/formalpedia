-- Prove2me | Theorems.Thm_FullFormalization_convexOn_le_gradient
-- name    : FullFormalization.convexOn_le_gradient
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:32:32.204784+00:00
-- url     : https://prove2.me/theorems/05fc51c8-140d-4ab7-b209-3739479d145b
-- title:
--   First-order inequality for convex differentiable functions
-- statement:
--   Let $f$ be a convex, differentiable function on a real inner product space $E$, and let $x, y \in E$. Then $f$ lies above its first-order Taylor expansion at $x$:
--   $$f(x) + \langle \nabla f(x),\, y - x\rangle \le f(y),$$
--   where $\nabla f(x)$ is the gradient of $f$ at $x$ and $\langle\cdot,\cdot\rangle$ is the inner product of $E$. This first-order characterisation of convexity is what turns a vanishing gradient into a global optimality certificate, and the source uses it at line 235 to conclude that $x_j$ minimises $\phi = f - \langle g_j, \cdot\rangle$ in the proof of (2.2).
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §2, eq. (2.2) (source lines 211-279, esp. line 235); Lean: FullFormalization.SmoothConvex lines 90-126

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

theorem FullFormalization.convexOn_le_gradient {f : E → ℝ} (hconv : ConvexOn ℝ Set.univ f)
    (hd : Differentiable ℝ f) (x y : E) :
    f x + ⟪∇ f x, y - x⟫ ≤ f y := by sorry
