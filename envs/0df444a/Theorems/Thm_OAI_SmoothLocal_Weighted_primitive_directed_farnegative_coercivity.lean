-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Weighted_primitive_directed_farnegative_coercivity
-- name    : OAI.SmoothLocal.Weighted.primitive_directed_farnegative_coercivity
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:51.998905+00:00
-- url     : https://prove2.me/theorems/f48773bb-6ae1-4064-aed1-816186c27c51
-- title:
--   Directed multiplier is coercive where $A$ is far from zero on the negative side
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $B$ be smooth on a coordinate rectangle, $p$ in the rectangle with $s<\mathrm{edge}$ and $A(p)\le-\alpha<0$, $A$ differentiable at $p$, $C(p)=(\ell+1)\partial_sA(p)+A(p)r(p)$, and let $\lambda>0$, $0\le\epsilon\le1$, $\mu>0$ satisfy the listed budgets in terms of bounds $M_I,M_B,M_r,M_A,M_{A_s},M_{A_t}$ for the primitive $I=\int_0^tB\,dr$, $B$, $r$ and $A$ at $p$. Then for all real $x,y$,
--
--   $$\min\Big(\frac\lambda8,\frac\mu2\Big)W(p)(x^2+y^2)\le T(p)x^2+S_0(p)y^2+J(p)xy,$$
--
--   with $W=d^8e^{-\lambda s+I}$ the directed weight, and $T,S_0,J$ the coefficients (3.14) for $m=-W$, $n=\epsilon tW$.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Weighted.primitive_directed_farnegative_coercivity` in `lean/OAI/Geometry/IsometricImmersion/Energy/DirectedFarNegative.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Energy/DirectedFarNegative.lean; Section 3.2, (3.15)-(3.16)

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem primitive_directed_farnegative_coercivity
    {B : Coord → ℝ} {R a b : ℝ} {p : Coord}
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (A C r : Coord → ℝ)
    (hA : DifferentiableAt ℝ A p) (edge lambda epsilon : ℝ) (ell : ℕ)
    (hedge : p 1 < edge) (hlambda : 0 < lambda)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hC : C p = ((ell : ℝ) + 1) * coordPartial 1 A p + A p * r p)
    (MI MB Mr MA MAs MAt mu alpha : ℝ) (hmu : 0 < mu)
    (hIs : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI)
    (hBp : |B p| ≤ MB) (hr : |r p| ≤ Mr)
    (hAp : |A p| ≤ MA) (hAs : |coordPartial 1 A p| ≤ MAs)
    (hTbudget : 2 * (MI + epsilon + epsilon * R * MB) ≤ lambda)
    (hEbudget : (MI + 1 + R * MB) / 2 + Mr ≤ lambda / 8)
    (hsmall : 4 * (R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)) ^ 2 *
      epsilon ^ 2 * MA ≤ 1 / 8)
    (hloss : (4 * (R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)) ^ 2 *
      epsilon ^ 2) / lambda ≤ mu / 4)
    (hAt : |coordPartial 0 A p| ≤ MAt)
    (halpha : 0 < alpha) (hAfar : A p ≤ -alpha)
    (hdominance : directedPrincipalBound ell epsilon R MAs MAt + mu ≤ lambda * alpha / 4)
    (x y : ℝ) :
    min (lambda / 8) (mu / 2) * directedWeight edge lambda (coordinatePrimitive B) p *
      (x ^ 2 + y ^ 2) ≤
      multiplierT B (directedM edge lambda (coordinatePrimitive B))
          (directedN edge lambda epsilon (coordinatePrimitive B)) p * x ^ 2 +
        multiplierS A C (directedM edge lambda (coordinatePrimitive B))
          (directedN edge lambda epsilon (coordinatePrimitive B)) p * y ^ 2 +
        multiplierJ A B C (directedM edge lambda (coordinatePrimitive B))
          (directedN edge lambda epsilon (coordinatePrimitive B)) p * x * y := by
  sorry

end SmoothLocal.Weighted
end
end OAI
