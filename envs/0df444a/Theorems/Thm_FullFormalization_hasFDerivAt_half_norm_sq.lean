-- Prove2me | Theorems.Thm_FullFormalization_hasFDerivAt_half_norm_sq
-- name    : FullFormalization.hasFDerivAt_half_norm_sq
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T06:02:00.309502+00:00
-- url     : https://prove2.me/theorems/dada5a38-2e82-4f2a-a869-dc25eb0c1753
-- title:
--   Fréchet derivative of $\tfrac12\|P_{u^\perp}\cdot\|^{2}$
-- statement:
--   For a unit vector $u$ ($\|u\| = 1$), the map $y \mapsto \tfrac12\|P_{u^{\perp}} y\|^{2}$ — half the squared norm of the component of $y$ orthogonal to $u$ — is Fréchet differentiable, with derivative
--
--   $$D_z\Bigl[\tfrac12\|P_{u^{\perp}}\cdot\|^{2}\Bigr] = P_{u^{\perp}} z,$$
--
--   the functional $y \mapsto \langle P_{u^{\perp}} z,\,y\rangle$, where $P_{u^{\perp}} y = y - \langle u,y\rangle u$ is the orthogonal projection onto $u^{\perp}$. This is the $u^{\perp}$ summand of the lifted-Huber gradient (26.3).
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §26, eq. (26.3); Lean: FullFormalization.LiftedHuber lines 339-355

-- Generated from F:/20261008/FullFormalization\FullFormalization\LiftedHuber.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.LiftedHuber

  Source sections 25-26: the *common extremal function* of Theorem B.

  Fix `d j = j (j+7) / 8` (4.1) and a unit vector `u`.  With

      c = 1 / (2 d_N + 1)                                           (25.1)
      H_c(t) = t^2/2  for |t| ≤ c,   c |t| - c^2/2  for |t| ≥ c     (25.2)

  the source defines

      f_N(z) = H_c(⟪u,z⟫ - 1) + (1/2) ‖z - ⟪u,z⟫ u‖²                (25.3)

  Section 26 then records:

  * (26.1) the orthogonal decomposition `z = t u + w`, `w ⊥ u`, along which
    `f_N(z) = H_c(t - 1) + (1/2)‖w‖²`;
  * (26.2) the unique minimiser `z* = u`, `f_N* = 0`, `‖z*‖ = 1`;
  * (26.3) the gradient `∇f_N(z) = clip(⟪u,z⟫-1, -c, c) u + (z - ⟪u,z⟫ u)`,
    whose two summands live in the orthogonal subspaces `span u` and `u^⊥` and
    are each 1-Lipschitz, whence `f_N` is convex, differentiable and globally
    1-smooth;
  * (26.4)-(26.6) the linear-branch formulas on `t ≤ 1 - c`.

  Everything below is proved, nothing is postulated.  The single genuinely
  analytic point is `hasDerivAt_Hc`: the Huber function is differentiable
  everywhere, including at the two kinks `t = ±c`, where the quadratic and
  linear branches paste together smoothly.  Those two points are handled by
  gluing the one-sided derivatives with `HasDerivWithinAt.union`.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_LiftedHuber
import Theorems.Thm_FullFormalization_hasFDerivAt_orthProj
import Theorems.Thm_FullFormalization_inner_orthProj
import Theorems.Thm_FullFormalization_inner_orthProj_left
import Theorems.Thm_FullFormalization_inner_u_self
import Theorems.Thm_FullFormalization_orthProjL_apply

open scoped Gradient RealInnerProductSpace Topology
open Set
open InnerProductSpace

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### The clipping map of (26.3) -/

















/-! ### The Huber function (25.2) -/













/-! ### Differentiability of the Huber function

The only non-elementary point is `|t| = c`, where the branch is a smooth paste
of `t²/2` and `c|t| - c²/2`: on `Iic c` the function agrees with `t²/2` near
`c`, on `Ici c` it agrees with `c t - c²/2`, and both one-sided derivatives at
`c` equal `c`.  The two one-sided statements are glued with
`HasDerivWithinAt.union`. -/







/-! ### Orthogonal decomposition in the direction `u` -/

















/-! ### The gradient of `H_c(⟪u,·⟫ - 1)` -/



/-! ### The gradient of `(1/2)‖z - ⟪u,z⟫ u‖²` -/



/-! ### The lifted Huber function (25.3) -/











/-! ### The gradient (26.3) -/







/-! ### Convexity, via monotonicity of the gradient -/







/-! ### The gradient is globally 1-Lipschitz

The first summand of (26.3) lies in `span u`, the second in `u^⊥`; the two
components of `a - b` decompose the same way, so Pythagoras reduces the claim to
the 1-Lipschitzness of the clipping. -/



/-! ### The minimum of the lifted Huber function (26.2) -/







/-! ### The linear branch (26.4)-(26.6) -/





/-! ### The source's cutoff, and the specialization to `liftedHuber` -/





























end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace Topology
open Set
open InnerProductSpace
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem FullFormalization.hasFDerivAt_half_norm_sq (u z : E) (hu : ‖u‖ = 1) :
    HasFDerivAt (fun y : E => (1 / 2) * ‖orthProj u y‖ ^ 2) (toDual ℝ E (orthProj u z)) z := by sorry
