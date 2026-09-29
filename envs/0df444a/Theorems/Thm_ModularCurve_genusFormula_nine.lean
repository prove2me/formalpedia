-- Prove2me | Theorems.Thm_ModularCurve_genusFormula_nine
-- name    : ModularCurve.genusFormula_nine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/f642e959-ccd1-58f2-8c58-5328315232d6
-- title:
--   The genus formula for X₀(N) vanishes at N=9
-- statement:
--   The statement is a closed numerical identity with no variables or hypotheses: the rational number [`ModularCurve.genusFormula 9`](def/ModularCurve_GenusNumerics.html#L20) is equal to $0$. Here `genusFormula N` is defined as the rational combination $1 + \psi(N)/12 - \nu_2(N)/4 - \nu_3(N)/3 - \nu_\infty(N)/2$, where: `dedekindPsi N` is the natural number $\sum_{d \mid N,\ d \text{ squarefree}} N/d$; `nuTwo N` is the cardinality of the set of $x \in \mathbb{Z}/N$ with $x^2 + 1 = 0$; `nuThree N` is the cardinality of the set of $x \in \mathbb{Z}/N$ with $x^2 + x + 1 = 0$; and `cuspCount N` is $\sum_{d \mid N} \varphi(\gcd(d, N/d))$, with $\varphi$ Euler's totient. Thus the assertion is the arithmetic fact that at $N = 9$ these four quantities take the values $12$, $0$, $0$ and $4$, so that $1 + 12/12 - 0/4 - 0/3 - 4/2 = 0$. Note that the theorem is purely a statement about the value of this rational expression: no modular curve, no Riemann surface and no genus is mentioned in it.
--
--   The expression evaluated here is the classical Riemann–Hurwitz genus formula for the modular curve $X_0(N)$, whose ingredients are the index-type quantity $\psi(N)$, the numbers of elliptic points of orders $2$ and $3$, and the number of cusps; its vanishing at $N = 9$ records that $X_0(9)$ has genus zero. It is used as the numerical input for [`CuspForm.eq_zero_of_level_dvd_four_or_dvd_nine`](thm.html#CuspForm.eq_zero_of_level_dvd_four_or_dvd_nine), the vanishing of weight-two cusp forms of level dividing $4$ or $9$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genusFormula_nine.lean

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.genusFormula_nine : ModularCurve.genusFormula 9 = 0 := by sorry
