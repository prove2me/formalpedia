-- Prove2me | Theorems.Thm_ModularCurve_toricPoint_fst_coeff_zero
-- name    : ModularCurve.toricPoint_fst_coeff_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/2e5a9e19-e6f0-5939-b36c-126ada884b08
-- title:
--   Constant term of the toric point's x-coordinate
-- statement:
--   Let $K$ be a field, let $p$ be a natural number and let $c$ be an element of $K$. The pair `toricPoint K p c` consists of two Laurent series over $K$, each obtained from an explicitly given power series in the variable $q$ by the inclusion of power series into Laurent series (Hahn series over $\mathbb{Z}$); the first component is the series whose $m$-th coefficient is $c/(1-c)^2$ when $m = 0$, and otherwise $\sum_{d \mid m,\ p \mid d} (m/d)\bigl(c^{m/d} + c^{-(m/d)}\bigr) - 2\,[\,p \mid m\,]\sum_{e \mid m/p} e$. The assertion is that the coefficient of this first component at the index $0 \in \mathbb{Z}$ equals $c/(1-c)^2$, i.e. the value at $u = c$ of the rational function $u/(1-u)^2$. No hypothesis is imposed on $c$ or on $p$ beyond $K$ being a field: in particular $c$ is not required to be non-zero or different from $1$, the expression $c/(1-c)^2$ being interpreted by Lean's convention for division.
--
--   In the Tate parametrisation, the point of multiplicative parameter $u$ on the Tate curve has $x$-coordinate $u/(1-u)^2$ plus corrections in positive powers of $q$; this statement records the constant term of the $x$-series attached to the constant parameter $c$, the corrections being the divisor sums supported on exponents divisible by $p$. It is used in the verification that these series satisfy the Tate curve equation ([`ModularCurve.tateUniv_equation`](thm.html#ModularCurve.tateUniv_equation), [`ModularCurve.toricPoint_equation`](thm.html#ModularCurve.toricPoint_equation)) and in the compatibility of toric points with the $q$-expansion and Vélu-type maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_toricPoint_fst_coeff_zero.lean

import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.toricPoint_fst_coeff_zero (K : Type*) [Field K] (p : ℕ) (c : K) : (toricPoint K p c).1.coeff 0 = c / (1 - c) ^ 2 := by sorry
