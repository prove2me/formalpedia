-- Prove2me | Theorems.Thm_ModularCurve_exists_linearIndependent_isModPFormFn_rat_dimFormula_le_card
-- name    : ModularCurve.exists_linearIndependent_isModPFormFn_rat_dimFormula_le_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/8fabcc0b-1b96-5600-b9ff-06752617c3a8
-- title:
--   Rational weight-2m forms of level N: dimension lower bound
-- statement:
--   Let $N$ be a positive natural number and let $m$ be a natural number with $1 \le m$. The assertion is that there exist a natural number $d$ and a family $Y : \mathrm{Fin}\ d \to \mathbb{Q}((q))$ of Laurent series over $\mathbb{Q}$ such that: each $Y_i$ lies in `modularFunctionFieldFull N`, the intermediate field of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the series $\mathrm{qExpand}\ \mathbb{Q}\ e\ jq$ for the nonzero divisors $e$ of $N$; each $Y_i$ satisfies `IsModPFormFn ℚ m`, i.e. $Y_i^6\, j^{4m} (j - 1728)^{3m}$ is integral over $\mathbb{Q}[j]$ and $Y_i^2\, j^{m} (j - 1728)^{m}$ is integral over $\mathbb{Q}[j^{-1}]$, where $j$ denotes `jqModC ℚ`, the $q$-expansion of the modular invariant as a Laurent series; the family $Y$ is linearly independent over $\mathbb{Q}$; and, finally, $d$ is at least $$(2m-1)(g_N-1) + \lfloor m/2 \rfloor \nu_2(N) + \lfloor 2m/3 \rfloor \nu_3(N) + m\,\nu_\infty(N),$$ the floors being natural-number divisions, where $\nu_2(N)$ is the number of $x \in \mathbb{Z}/N$ with $x^2+1=0$, $\nu_3(N)$ the number with $x^2+x+1=0$, $\nu_\infty(N) = \sum_{d \mid N} \varphi(\gcd(d, N/d))$, and $g_N = 1 + \psi(N)/12 - \nu_2(N)/4 - \nu_3(N)/3 - \nu_\infty(N)/2$ with $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$.
--
--   The right-hand side of the inequality is the classical formula for $\dim_{\mathbb{C}} M_{2m}(\Gamma_0(N))$ in terms of the genus of $X_0(N)$, its elliptic points of orders $2$ and $3$, and its cusps; the statement thus produces that many $\mathbb{Q}$-linearly independent weight-$2m$ forms of level $N$ with rational $q$-expansions, in the integrality formulation of holomorphy. It is the rational-coefficient form, obtained by Galois descent from the corresponding statement over $\overline{\mathbb{Q}}$, and it feeds the construction of forms with integral $q$-coefficients in [`ModularForm.exists_linearIndependent_int_qCoeff_dimFormula_le_card`](thm.html#ModularForm.exists_linearIndependent_int_qCoeff_dimFormula_le_card).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearIndependent_isModPFormFn_rat_dimFormula_le_card.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_linearIndependent_isModPFormFn_rat_dimFormula_le_card
    (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m) :
    ∃ (d : ℕ) (Y : Fin d → LaurentSeries ℚ),
      (∀ i, Y i ∈ modularFunctionFieldFull N) ∧ (∀ i, IsModPFormFn ℚ m (Y i)) ∧ LinearIndependent ℚ Y ∧
      (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1)
        + ((m / 2 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ) + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ)
        + (m : ℚ) * (ModularCurve.cuspCount N : ℚ) ≤ (d : ℚ) := by sorry
