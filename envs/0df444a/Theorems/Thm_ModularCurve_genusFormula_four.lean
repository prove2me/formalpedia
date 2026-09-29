-- Prove2me | Theorems.Thm_ModularCurve_genusFormula_four
-- name    : ModularCurve.genusFormula_four
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/593a73b8-9c68-51d2-80f8-e52f227a401f
-- title:
--   The genus formula vanishes at level 4
-- statement:
--   The statement is a closed numerical evaluation: the rational number [`ModularCurve.genusFormula 4`](def/ModularCurve_GenusNumerics.html#L20) equals $0$. Here, for a natural number $N$, $$\mathtt{genusFormula}(N) = 1 + \frac{\psi(N)}{12} - \frac{\nu_2(N)}{4} - \frac{\nu_3(N)}{3} - \frac{\nu_\infty(N)}{12}\cdot 6,$$ more precisely $1 + \psi(N)/12 - \nu_2(N)/4 - \nu_3(N)/3 - \nu_\infty(N)/2$ computed in $\mathbb{Q}$, where the four integer inputs are defined by: $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$ (the Dedekind $\psi$-function, given here by this divisor sum); $\nu_2(N)$ is the cardinality of the set of $x \in \mathbb{Z}/N$ with $x^2 + 1 = 0$; $\nu_3(N)$ is the cardinality of the set of $x \in \mathbb{Z}/N$ with $x^2 + x + 1 = 0$; and $\nu_\infty(N) = \sum_{d \mid N} \varphi(\gcd(d, N/d))$. There are no hypotheses or variables. At $N = 4$ the four quantities are $\psi(4) = 6$, $\nu_2(4) = 0$, $\nu_3(4) = 0$ and $\nu_\infty(4) = 3$, so that $1 + 6/12 - 0 - 0 - 3/2 = 0$. The assertion is purely arithmetical: it concerns the value of the stated rational expression, not a geometric genus of a curve.
--
--   Classically this is the statement that the modular curve $X_0(4)$ has genus zero, $4$ being one of the genus-zero levels for $\Gamma_0(N)$. It is used as the numerical input to [`CuspForm.eq_zero_of_level_dvd_four_or_dvd_nine`](thm.html#CuspForm.eq_zero_of_level_dvd_four_or_dvd_nine), the vanishing of the space of weight-two cusp forms of level $4$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genusFormula_four.lean

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.genusFormula_four : ModularCurve.genusFormula 4 = 0 := by sorry
