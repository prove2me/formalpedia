-- Prove2me | Theorems.Thm_HodgeComputer_ReflectionChart_relative_primitive_of_canonical_trace
-- name    : HodgeComputer.ReflectionChart.relative_primitive_of_canonical_trace
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T04:57:41.8956+00:00
-- url     : https://prove2.me/theorems/50907190-8358-42f0-ac43-d647e3439a5b
-- title:
--   Canonical linear-in-u trace reduction for cubic threefolds with up-to-cubic sources
-- statement:
--   Consider a family of affine cubic threefolds
--
--   $$
--   f(\lambda, b, c, d, u) = \ell(\lambda) u^3 + c_2(\lambda, b, c, d) u^2 + c_1(\lambda, b, c, d) u + c_0(\lambda, b, c, d)
--   $$
--
--   whose leading coefficient $\ell(\lambda)$ depends only on the pencil parameter $\lambda$ and satisfies $\ell(0) \neq 0$, while $f(\lambda, b, c, d, v^2)$ is irreducible and vanishes at $(0, 0, 0, 0, i)$. Let $P = p_0 + p_1 u + p_2 u^2 + p_3 u^3$ be any polynomial source of degree at most $3$ in $u$ with $u$-independent coefficients $p_0, p_1, p_2, p_3 \in \mathbb{C}[\lambda, b, c, d]$, and define
--
--   $$
--   K_0 = 6 \ell^2 p_0 - 2 \ell c_1 p_2 + (3 \ell c_0 + c_2 c_1) p_3, \qquad K_1 = 6 \ell^2 p_1 - 4 \ell c_2 p_2 + 2 c_2^2 p_3.
--   $$
--
--   If $f$ admits a cleared relative primitive for the **linear-in-$u$** canonical trace source $K_0 + K_1 u$, then $f$ admits a cleared relative primitive for $P$ itself.
--
--   The reduction rests on the exact polynomial identity
--
--   $$
--   6 \ell^2 (f_u P_u - f_{uu} P) = \bigl(f_u K_1 - f_{uu}(K_0 + K_1 u)\bigr) + 6 \ell p_3 (3 \ell u + c_2) f,
--   $$
--
--   which simultaneously removes the $u^3$ pole (via $f_u^2$ modulo $f$) and the $u^2$ branch multiple of $f_u$, together with the fact that $E = 6 \ell(\lambda)^2$ is constant along the fiber derivatives $(\partial_b, \partial_c, \partial_d, \partial_u)$.
--
--   **Formalization Note** Scaling a witness $(D, C_{\mathrm{vec}})$ for $K_0 + K_1 u$ to $(6 \ell^2 D, C_{\mathrm{vec}})$ preserves relative primality to $f$ because $f$ is irreducible and $\ell(0) \neq 0$.
-- source:
--   Generalization of the quadratic canonical trace identity in Hodge.computer Discussion #117 (`fqlx`, `benediamond`, `kmehltretter82`) to degree-three reflection sources such as `diagonal-permutation` (Discussion #177), https://github.com/hodge-computer/sextics/discussions/177

import Definitions.Def_HodgeComputerReflectionChart
import Mathlib.RingTheory.Polynomial.UniqueFactorization

theorem HodgeComputer.ReflectionChart.relative_primitive_of_canonical_trace
    (f P ell c2 c1 c0 p0 p1 p2 p3 : HodgeComputer.ReflectionChart.ChartPoly)
    (hf : f = ell * MvPolynomial.X 4 ^ 3 + c2 * MvPolynomial.X 4 ^ 2 + c1 * MvPolynomial.X 4 + c0)
    (hP : P = p0 + p1 * MvPolynomial.X 4 + p2 * MvPolynomial.X 4 ^ 2 + p3 * MvPolynomial.X 4 ^ 3)
    (hH_irred : Irreducible (HodgeComputer.ReflectionChart.squareLift f))
    (h_pt_zero : MvPolynomial.eval HodgeComputer.ReflectionChart.normalPoint
      (HodgeComputer.ReflectionChart.squareLift f) = 0)
    (h_pt_ell : MvPolynomial.eval HodgeComputer.ReflectionChart.normalPoint
      (HodgeComputer.ReflectionChart.squareLift ell) ≠ 0)
    (hell_base : ∀ k : Fin 4, MvPolynomial.pderiv k.succ ell = 0)
    (hc2_u : MvPolynomial.pderiv 4 c2 = 0)
    (hc1_u : MvPolynomial.pderiv 4 c1 = 0)
    (hc0_u : MvPolynomial.pderiv 4 c0 = 0)
    (hp0_u : MvPolynomial.pderiv 4 p0 = 0)
    (hp1_u : MvPolynomial.pderiv 4 p1 = 0)
    (hp2_u : MvPolynomial.pderiv 4 p2 = 0)
    (hp3_u : MvPolynomial.pderiv 4 p3 = 0)
    (h_lin : HodgeComputer.ReflectionChart.RelativePrimitive f
      (HodgeComputer.ReflectionChart.cubicTraceK0 ell c2 c1 c0 p0 p2 p3 +
        HodgeComputer.ReflectionChart.cubicTraceK1 ell c2 p1 p2 p3 * MvPolynomial.X 4)) :
    HodgeComputer.ReflectionChart.RelativePrimitive f P := by sorry
