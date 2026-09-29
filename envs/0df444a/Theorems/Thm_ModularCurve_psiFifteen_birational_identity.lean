-- Prove2me | Theorems.Thm_ModularCurve_psiFifteen_birational_identity
-- name    : ModularCurve.psiFifteen_birational_identity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/3f0158ec-652f-5317-8e2c-1e7efc2850cf
-- title:
--   Birational map from Ψ₁₅=0 to the curve 15a1
-- statement:
--   Let $u,v$ be rational numbers satisfying the relation $(u+27)(u+3)^3 v - u(v^2+10v+5)^3 = 0$, and let $N_x, D_x, N_y, D_y$ be rational numbers given by the four explicit integer polynomial expressions in $u$ and $v$: $N_x = 135 - 1701v - 972v^2 - 108v^3 + 250u - 146uv - 12uv^2 - 8uv^3 + 15u^2 - 13u^2v$, $D_x = 1458v + 621v^2 + 54v^3 - 250u - 7uv - 24uv^2 - uv^3 - 15u^2 + 4u^2v$, $N_y = 64125 - 196047v - 86022v^2 - 5778v^3 + 10125u - 79605uv - 10035uv^2 + 225uv^3 - 432u^2v + 63u^2v^2 + 27u^2v^3 + 90u^3v$ and $D_y = 134136v + 43011v^2 + 2889v^3 - 23000u + 290uv + 2930uv^2 + 225uv^3 - 1125u^2 - 484u^2v - 44u^2v^2 - u^2v^3 + 5u^3v$. Then $$N_y^2 D_x^3 + N_x N_y D_x^2 D_y + N_y D_x^3 D_y - N_x^3 D_y^2 - N_x^2 D_x D_y^2 + 10 N_x D_x^2 D_y^2 + 10 D_x^3 D_y^2 = 0.$$ This is the equation $y^2 + xy + y = x^3 + x^2 - 10x - 10$ for $x = N_x/D_x$, $y = N_y/D_y$, cleared of denominators by $D_x^3 D_y^2$; no non-vanishing of $D_x$ or $D_y$ is assumed, and the assertion is an identity between rational numbers rather than a statement about points of a curve.
--
--   The relation imposed on $(u,v)$ is the affine plane model of $X_0(15)$ obtained as the fibre product of the $j$-maps $j = (u+27)(u+3)^3/u$ on $X_0(3)$ and $j = (v^2+10v+5)^3/v$ on $X_0(5)$, and the four polynomials are the numerators and denominators of an explicit rational map from this model to the elliptic curve $y^2+xy+y = x^3+x^2-10x-10$ of conductor $15$. It is used by [`ModularCurve.fifteenIsogenyJ_of_hauptmodul_memberships`](thm.html#ModularCurve.fifteenIsogenyJ_of_hauptmodul_memberships), in the determination of the $j$-invariants of elliptic curves over $\mathbb{Q}$ admitting a rational $15$-isogeny.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_psiFifteen_birational_identity.lean

import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.psiFifteen_birational_identity (u v : ℚ)
    (hpsi : (u + 27) * (u + 3) ^ 3 * v - u * (v ^ 2 + 10 * v + 5) ^ 3 = 0)
    (Nx Dx Ny Dy : ℚ)
    (hNx : Nx = 135 - 1701 * v - 972 * v ^ 2 - 108 * v ^ 3 + 250 * u - 146 * u * v
      - 12 * u * v ^ 2 - 8 * u * v ^ 3 + 15 * u ^ 2 - 13 * u ^ 2 * v)
    (hDx : Dx = 1458 * v + 621 * v ^ 2 + 54 * v ^ 3 - 250 * u - 7 * u * v - 24 * u * v ^ 2
      - u * v ^ 3 - 15 * u ^ 2 + 4 * u ^ 2 * v)
    (hNy : Ny = 64125 - 196047 * v - 86022 * v ^ 2 - 5778 * v ^ 3 + 10125 * u - 79605 * u * v
      - 10035 * u * v ^ 2 + 225 * u * v ^ 3 - 432 * u ^ 2 * v + 63 * u ^ 2 * v ^ 2
      + 27 * u ^ 2 * v ^ 3 + 90 * u ^ 3 * v)
    (hDy : Dy = 134136 * v + 43011 * v ^ 2 + 2889 * v ^ 3 - 23000 * u + 290 * u * v
      + 2930 * u * v ^ 2 + 225 * u * v ^ 3 - 1125 * u ^ 2 - 484 * u ^ 2 * v - 44 * u ^ 2 * v ^ 2
      - u ^ 2 * v ^ 3 + 5 * u ^ 3 * v) :
    Ny ^ 2 * Dx ^ 3 + Nx * Ny * Dx ^ 2 * Dy + Ny * Dx ^ 3 * Dy - Nx ^ 3 * Dy ^ 2
      - Nx ^ 2 * Dx * Dy ^ 2 + 10 * Nx * Dx ^ 2 * Dy ^ 2 + 10 * Dx ^ 3 * Dy ^ 2 = 0 := by sorry
