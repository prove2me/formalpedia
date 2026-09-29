-- Prove2me | Theorems.Thm_ModularCurve_legendreJ_eq_ofNat_iff
-- name    : ModularCurve.legendreJ_eq_ofNat_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/81e3e953-a55e-58db-9d0a-28a317e88fcf
-- title:
--   j(λ)=1728 exactly for λ∈{-1,2,1/2}
-- statement:
--   Let $K$ be a field in which $2 \neq 0$, and let $t \in K$ satisfy $t \neq 0$ and $t \neq 1$. Here `legendreJ t` denotes the element $2^8 (t^2 - t + 1)^3 / (t^2 (t-1)^2)$ of $K$, the Legendre $j$-invariant of the parameter $t$. The theorem asserts the equivalence: `legendreJ t` equals $1728$ if and only if $t = -1$, or $t = 2$, or $t = 2^{-1}$ (the inverse taken in $K$, which is legitimate since $2 \neq 0$). Both hypotheses $t \neq 0$, $t \neq 1$ serve to make the denominator $t^2(t-1)^2$ nonzero, so that the quotient defining `legendreJ` is not the junk value $0$ arising from division by zero; no hypothesis on the characteristic beyond $2 \neq 0$ is imposed, so in particular the three listed values need not be pairwise distinct (they coincide in characteristic $3$).
--
--   This identifies the fibre over $j = 1728$ of the Legendre parametrisation $\lambda \mapsto j(\lambda)$, the anharmonic orbit $\{-1, 2, 1/2\}$ of the $S_3$-action on the $\lambda$-line corresponding to curves with extra automorphisms, such as $y^2 = x^3 + x$. It is used in the computation of orbit sizes against ramification weights in [`ModularCurve.card_orbit_mul_jWidth`](thm.html#ModularCurve.card_orbit_mul_jWidth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_legendreJ_eq_ofNat_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_LegendreJ

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.legendreJ_eq_ofNat_iff {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 1728 ↔ t = -1 ∨ t = 2 ∨ t = 2⁻¹ := by sorry
