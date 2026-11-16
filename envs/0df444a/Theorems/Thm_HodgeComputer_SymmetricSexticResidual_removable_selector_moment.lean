-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_removable_selector_moment
-- name    : HodgeComputer.SymmetricSexticResidual.removable_selector_moment
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-16T05:48:23.297957+00:00
-- url     : https://prove2.me/theorems/06ef0f15-636c-459e-8966-2dc0538061ef
-- title:
--   Symmetric sextic: removable selector moment and pivot nonvanishing
-- statement:
--   Consider a cubic polynomial $f(x, u) = \ell u^3 + B(x) u^2 + C(x) u + D(x)$ over $\mathbb{C}$ with $\ell \neq 0$ independent of $x$, where $B(x) = b_0 + b_1 x$, $C(x) = c_0 + c_1 x + c_2 x^2$, and $D(x) = d_0 + d_1 x + d_2 x^2 + d_3 x^3$. Write $g = f_u$, $g_u = f_{uu}$, $f_x = B_x u^2 + C_x u + D_x$, and $g_x = 2 B_x u + C_x$, and define the rational source pair
--
--   $$K_0 = \frac{-B C + 4 x B_x C + 9 \ell D - 12 \ell x D_x}{12 \ell}, \qquad K_1 = \frac{-B^2 + 4 x B B_x + 3 \ell C - 6 \ell x C_x}{6 \ell}.$$
--
--   Then:
--
--   1. The cleared polynomial certificate
--
--   $$g^2 - 2 x g g_x + 2 x f_x g_u - 2\bigl(g K_1 - g_u(K_0 + K_1 u)\bigr) = 3(B + 3\ell u) f$$
--
--   holds identically.
--
--   2. The pair $(K_0, K_1)$ expands as polynomials in $x$ of degrees at most $3$ and $2$, respectively, with leading $x^2$-coefficient $[x^2] K_1 = \frac{b_1^2 - 3 \ell c_2}{2 \ell}$.
--
--   3. For the symmetric sextic ratio pencil $(\ell, B_1, C_2)$ in $(\lambda, s)$, at $(\lambda, s) = (1, 0)$ we have $\ell \neq 0$ and $[x^2] K_1 = \frac{47425}{182} \neq 0$.
--
--   This identity absorbs one of the seven normalized-trace selector moment conditions by an explicit vertical rational current.
-- source:
--   https://github.com/hodge-computer/sextics/discussions/117#discussioncomment-19498520 (symmetric-contact-current/source/selector/REMOVABLE_SELECTOR_MOMENT.md)

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem HodgeComputer.SymmetricSexticResidual.removable_selector_moment
    (x u l b0 b1 c0 c1 c2 d0 d1 d2 d3 lam s : ℂ) :
    let B := b0 + b1 * x
    let Bx := b1
    let C := c0 + c1 * x + c2 * x ^ 2
    let Cx := c1 + 2 * c2 * x
    let D := d0 + d1 * x + d2 * x ^ 2 + d3 * x ^ 3
    let Dx := d1 + 2 * d2 * x + 3 * d3 * x ^ 2
    let f := l * u ^ 3 + B * u ^ 2 + C * u + D
    let g := 3 * l * u ^ 2 + 2 * B * u + C
    let gu := 6 * l * u + 2 * B
    let fx := Bx * u ^ 2 + Cx * u + Dx
    let gx := 2 * Bx * u + Cx
    let K0 := (-B * C + 4 * x * Bx * C + 9 * l * D - 12 * l * x * Dx) / (12 * l)
    let K1 := (-B ^ 2 + 4 * x * B * Bx + 3 * l * C - 6 * l * x * Cx) / (6 * l)
    let ell := 2 + 2 * lam ^ 6 - (5 / 7 : ℂ) * lam ^ 2 - (10 / 7 : ℂ) * lam ^ 4
    let actualB1 := 30 * lam ^ 4 + (5 / 7 : ℂ) * (1 + 2 * s) +
      (20 / 7 : ℂ) * lam ^ 2 * (1 + 2 * s)
    let actualC2 := 30 * lam ^ 2 - (10 / 7 : ℂ) * (1 + 2 * s) ^ 2
    (l ≠ 0 →
      (g ^ 2 - 2 * x * g * gx + 2 * x * fx * gu - 2 * (g * K1 - gu * (K0 + K1 * u)) =
        3 * (B + 3 * l * u) * f) ∧
      (K0 = (-b0 * c0 + 9 * l * d0) / (12 * l) +
            ((3 * b1 * c0 - b0 * c1 - 3 * l * d1) / (12 * l)) * x +
            ((3 * b1 * c1 - b0 * c2 - 15 * l * d2) / (12 * l)) * x ^ 2 +
            ((3 * b1 * c2 - 27 * l * d3) / (12 * l)) * x ^ 3) ∧
      (K1 = (-b0 ^ 2 + 3 * l * c0) / (6 * l) +
            ((2 * b0 * b1 - 3 * l * c1) / (6 * l)) * x +
            ((b1 ^ 2 - 3 * l * c2) / (2 * l)) * x ^ 2)) ∧
    (lam = 1 → s = 0 →
      ell ≠ 0 ∧ (actualB1 ^ 2 - 3 * ell * actualC2) / (2 * ell) = (47425 / 182 : ℂ)) := by sorry
