-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_mk_sphericalTorusValue_mul_coe_eq_one_and_hasSum
-- name    : LanglandsTunnell.CubicInduction.mk_sphericalTorusValue_mul_coe_eq_one_and_hasSum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/e84a3b65-9cba-5040-a972-fe49ccc41716
-- title:
--   Generating series and convergence disc for cubic torus values
-- statement:
--   Let $P \in \mathbb{C}[X]$ be a polynomial with $P$'s constant coefficient equal to $1$ and $\deg P \le 3$ (natural-degree at most $3$). Write $a_i = P_{(i)}$ for the coefficient of $X^i$, and let $h : \mathbb{N} \to \mathbb{C}$ be the sequence `sphericalTorusValue` evaluated at the triple $(e_1,e_2,e_3) = (-a_1, a_2, -a_3)$, i.e. $h_0 = 1$, $h_1 = e_1$, $h_2 = e_1^2 - e_2$ and $h_{n+3} = e_1 h_{n+2} - e_2 h_{n+1} + e_3 h_n$. Set $M = \max\bigl(1, \|a_1\| + \|a_2\| + \|a_3\|\bigr)$. The theorem asserts three things simultaneously: first, in $\mathbb{C}[[X]]$ the power series $\sum_{n \ge 0} h_n X^n$ times the image of $P$ equals $1$; second, $\|h_n\| \le M^n$ for every $n \in \mathbb{N}$; third, for every $x \in \mathbb{C}$ with $\|x\| \cdot M < 1$ one has $P(x) \ne 0$ and the family $n \mapsto h_n x^n$ is summable with sum $P(x)^{-1}$.
--
--   This is the generating-function identity $\sum_{n} h_n X^n = P(X)^{-1}$ for the complete homogeneous symmetric functions of the inverse roots of a cubic Euler factor, here for the recursively defined sequence used to pin down the torus values of the normalised spherical Whittaker function on $\mathrm{GL}_3$, together with the exponential bound that makes the series converge on the disc $\|x\| < M^{-1}$. It is used in the computation of the local factor at a place of good reduction, where the sum over the torus in the unramified local integral is identified with the inverse of the Euler polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_mk_sphericalTorusValue_mul_coe_eq_one_and_hasSum.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.mk_sphericalTorusValue_mul_coe_eq_one_and_hasSum
    (P : Polynomial ℂ) (hP0 : P.coeff 0 = 1) (hP3 : P.natDegree ≤ 3) :
    PowerSeries.mk (sphericalTorusValue (-P.coeff 1) (P.coeff 2) (-P.coeff 3)) * (P : PowerSeries ℂ) = 1 ∧
    (∀ n : ℕ, ‖sphericalTorusValue (-P.coeff 1) (P.coeff 2) (-P.coeff 3) n‖ ≤
      (max 1 (‖P.coeff 1‖ + ‖P.coeff 2‖ + ‖P.coeff 3‖)) ^ n) ∧
    ∀ x : ℂ, ‖x‖ * max 1 (‖P.coeff 1‖ + ‖P.coeff 2‖ + ‖P.coeff 3‖) < 1 →
      P.eval x ≠ 0 ∧
      HasSum (fun n : ℕ => sphericalTorusValue (-P.coeff 1) (P.coeff 2) (-P.coeff 3) n * x ^ n)
        (P.eval x)⁻¹ := by sorry
