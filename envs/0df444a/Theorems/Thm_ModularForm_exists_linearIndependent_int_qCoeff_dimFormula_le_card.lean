-- Prove2me | Theorems.Thm_ModularForm_exists_linearIndependent_int_qCoeff_dimFormula_le_card
-- name    : ModularForm.exists_linearIndependent_int_qCoeff_dimFormula_le_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/76f0c6d3-61b7-5967-b8fa-6c1306b35dea
-- title:
--   Integral weight-2m forms on Γ₀(N) attaining the dimension bound
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $m$ be a natural number with $1 \le m$. Then there exist a natural number $d$, a family $f : \mathrm{Fin}\,d \to M_{2m}(\Gamma_0(N))$ of modular forms of weight $2m$ (the weight being the integer $2\cdot m$) for the congruence subgroup $\Gamma_0(N)$, and integers $a_i(n) \in \mathbb{Z}$ indexed by $i \in \mathrm{Fin}\,d$ and $n \in \mathbb{N}$, such that: for all $i$ and $n$, the $n$-th coefficient of the $q$-expansion of width $1$ of $f_i$ equals the complex number $a_i(n)$; the family $f$ is linearly independent over $\mathbb{C}$; and, in $\mathbb{Q}$,
--   $$(2m-1)\bigl(g(N)-1\bigr) + \lfloor m/2 \rfloor\,\nu_2(N) + \lfloor 2m/3 \rfloor\,\nu_3(N) + m\,\nu_\infty(N) \le d,$$
--   where the two floors are the natural-number quotients $m/2$ and $(2m)/3$; $\nu_2(N)$ is the number of $x \in \mathbb{Z}/N$ with $x^2+1=0$; $\nu_3(N)$ the number of $x \in \mathbb{Z}/N$ with $x^2+x+1=0$; $\nu_\infty(N) = \sum_{d \mid N} \varphi(\gcd(d, N/d))$; and $g(N) = 1 + \psi(N)/12 - \nu_2(N)/4 - \nu_3(N)/3 - \nu_\infty(N)/2$ with $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$.
--
--   The right-hand side of the inequality is the classical formula for $\dim_{\mathbb{C}} M_{2m}(\Gamma_0(N))$ expressed through the genus formula and the counts of elliptic points of order $2$ and $3$ and of cusps of $X_0(N)$, so the statement provides that many $\mathbb{C}$-independent weight-$2m$ forms whose $q$-expansions at $\infty$ have rational integer coefficients. It feeds the lower-bound half of the mod-$p$ dimension comparison, being used by [`ModPForms.dimFormula_le_finrank_modPMod`](thm.html#ModPForms.dimFormula_le_finrank_modPMod).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_linearIndependent_int_qCoeff_dimFormula_le_card.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularForm.exists_linearIndependent_int_qCoeff_dimFormula_le_card (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m) :
    ∃ (d : ℕ) (f : Fin d → ModularForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ))) (a : Fin d → ℕ → ℤ),
      (∀ i n, ModularFormClass.qCoeff (f i) n = (a i n : ℂ)) ∧ LinearIndependent ℂ f ∧
      (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1)
        + ((m / 2 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ) + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ)
        + (m : ℚ) * (ModularCurve.cuspCount N : ℚ) ≤ (d : ℚ) := by sorry
