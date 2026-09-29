-- Prove2me | Theorems.Thm_ModPForms_dimFormula_le_finrank_modPMod
-- name    : ModPForms.dimFormula_le_finrank_modPMod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/badd26d1-895e-5b52-be0d-e7c6df8e68aa
-- title:
--   Dimension formula bounds the rank of reduced weight-2m forms
-- statement:
--   Fix a nonzero natural number $N$, a natural number $m$ with $m \ge 1$, and an arbitrary field $F$. Let [`ModPForms.modPMod N k F`](def/CuspForm_ModPForms.html#L12) denote the $F$-submodule of $F[[q]]$ spanned by all power series $\sum_n \bar a_n q^n$ arising as follows: $f$ is a modular form of weight $k$ on $\Gamma_0(N)$ and $a : \mathbb N \to \mathbb Z$ is an integer sequence with $\mathrm{qCoeff}(f)(n) = a_n$ in $\mathbb C$ for all $n$ (the coefficients of the $q$-expansion of $f$ with respect to width $1$), and $\bar a_n$ is the image of $a_n$ under $\mathbb Z \to F$. Write $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, $\nu_2(N) = \#\{x \in \mathbb Z/N : x^2+1 = 0\}$, $\nu_3(N) = \#\{x \in \mathbb Z/N : x^2+x+1 = 0\}$, $\nu_\infty(N) = \sum_{d \mid N} \varphi(\gcd(d, N/d))$, and $g(N) = 1 + \psi(N)/12 - \nu_2(N)/4 - \nu_3(N)/3 - \nu_\infty(N)/2$. Then, as an inequality of rational numbers,
--   $$(2m-1)\bigl(g(N)-1\bigr) + \lfloor m/2 \rfloor \nu_2(N) + \lfloor 2m/3 \rfloor \nu_3(N) + m\,\nu_\infty(N) \le \operatorname{finrank}_F \bigl(\mathrm{modPMod}\ N,\ 2m,\ F\bigr),$$
--   where the two floors are natural-number divisions $m/2$ and $2m/3$ and the weight is $2m$ viewed as an integer.
--
--   The right-hand side is the $F$-dimension of the space of mod-$p$ (or, more generally, mod-$F$) $q$-expansions obtained by reducing integral weight-$2m$ forms on $\Gamma_0(N)$, and the left-hand side is the classical complex dimension of $M_{2m}(\Gamma_0(N))$ expressed through the genus and ramification data of $X_0(N)$; the statement says that reduction does not lose dimension. It is used to produce enough mod-$p$ forms of a prescribed weight, in the construction of elements of `modPMod` with given $q$-expansion for functions satisfying the mod-$p$ form condition over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_dimFormula_le_finrank_modPMod.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.dimFormula_le_finrank_modPMod (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m) (F : Type) [Field F] :
    (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1)
      + ((m / 2 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ) + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ)
      + (m : ℚ) * (ModularCurve.cuspCount N : ℚ)
      ≤ (Module.finrank F ↥(ModPForms.modPMod N (2 * (m : ℤ)) F) : ℚ) := by sorry
