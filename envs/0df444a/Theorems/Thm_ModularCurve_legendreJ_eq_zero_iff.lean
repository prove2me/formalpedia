-- Prove2me | Theorems.Thm_ModularCurve_legendreJ_eq_zero_iff
-- name    : ModularCurve.legendreJ_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/a176a3ae-f0f9-572a-b6e8-80f8a3a15df0
-- title:
--   Vanishing of the Legendre j-invariant
-- statement:
--   Let $K$ be a field in which $2 \neq 0$, and let $t \in K$ satisfy $t \neq 0$ and $t \neq 1$. Here `legendreJ t` denotes the element $2^8 (t^2 - t + 1)^3 / \bigl(t^2 (t-1)^2\bigr)$ of $K$, the $j$-invariant attached to the Legendre parameter $t$. The assertion is the equivalence $$\mathrm{legendreJ}(t) = 0 \iff t^2 - t + 1 = 0.$$ Thus, under the two exclusions $t \neq 0, 1$ which make the denominator $t^2(t-1)^2$ invertible, and the hypothesis $2 \neq 0$ which makes the numerical factor $2^8$ invertible, the vanishing of the $j$-invariant is exactly the vanishing of the quadratic $t^2 - t + 1$; that is, $t$ is a primitive sixth root of unity in $K$ (equivalently $-t$ is a primitive cube root of unity), a condition involving no genericity assumption on the characteristic beyond $2 \neq 0$.
--
--   This is the standard characterisation of the fibre $j = 0$ of the Legendre parameter map $t \mapsto j(t)$, whose two roots form the anharmonic orbit under the $S_3$-action on the $\lambda$-line. It is used in [`ModularCurve.card_orbit_mul_jWidth`](thm.html#ModularCurve.card_orbit_mul_jWidth), where the orbits of that action and their sizes are compared with the ramification of the $j$-map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_legendreJ_eq_zero_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_LegendreJ

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.legendreJ_eq_zero_iff {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 0 ↔ t ^ 2 - t + 1 = 0 := by sorry
