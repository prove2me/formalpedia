-- Prove2me | Theorems.Thm_HeckeEis_finrank_coeffH1par_le_two_mul_dimFormula
-- name    : HeckeEis.finrank_coeffH1par_le_two_mul_dimFormula
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/4ef8529a-5a8c-5298-9937-0d3aa73d3421
-- title:
--   Upper bound for parabolic H¹ of Γ₀(N) in binary forms
-- statement:
--   Let $N\ge 1$ and let $n$ be a natural number with $2\le n$ and $n$ even. Consider the representation of $\mathrm{SL}_2(\mathbb Z)$ on the space $\mathrm{BinaryForm}\,\mathbb C\,n$ of homogeneous polynomials of degree $n$ in two variables over $\mathbb C$, where a matrix $M$ acts by the substitution $X_j\mapsto \sum_i M_{ij}X_i$, and restrict it along the inclusion of $\Gamma_0(N)$ into $\mathrm{SL}_2(\mathbb Z)$. The space [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) of this restricted representation is the quotient of the submodule of those functions $\Gamma_0(N)\to \mathrm{BinaryForm}\,\mathbb C\,n$ that are cocycles and satisfy the parabolicity condition `IsParabolicCocycle`, by the submodule of those among them lying in the image of the coboundary map. The assertion is the inequality, in $\mathbb Q$, $$\dim_{\mathbb C}\mathrm{coeffH1par}\le 2\Bigl[\bigl((n+2)-1\bigr)\bigl(g_N-1\bigr)+\lfloor (n+2)/4\rfloor\,\nu_2(N)+\lfloor (n+2)/3\rfloor\,\nu_3(N)+\bigl(\tfrac{n+2}{2}-1\bigr)\,c(N)\Bigr],$$ where the two floor terms are natural-number divisions cast into $\mathbb Q$ while $(n+2)/2$ is division in $\mathbb Q$; here $\nu_2(N)=\#\{x\in\mathbb Z/N: x^2+1=0\}$, $\nu_3(N)=\#\{x\in\mathbb Z/N: x^2+x+1=0\}$, $c(N)=\sum_{d\mid N}\varphi(\gcd(d,N/d))$, and $g_N=1+\psi(N)/12-\nu_2(N)/4-\nu_3(N)/3-c(N)/2$ with $\psi(N)=\sum_{d\mid N,\ d\ \text{squarefree}}N/d$.
--
--   The bracketed quantity is the classical dimension formula for $S_{n+2}(\Gamma_0(N))$ in terms of the genus and the numbers of elliptic points of order $2$, $3$ and of cusps of $X_0(N)$, so the statement is the easy half of the Eichler–Shimura comparison: parabolic cohomology in the $n$-th symmetric power is at most twice the space of cusp forms of weight $n+2$. It is used in establishing that the image of the Eichler–Shimura map and the image of its conjugate are complementary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_finrank_coeffH1par_le_two_mul_dimFormula.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.finrank_coeffH1par_le_two_mul_dimFormula (N : ℕ) [NeZero N] (n : ℕ) (hn : 2 ≤ n) (hne : Even n) :
    (Module.finrank ℂ (HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)) : ℚ)
      ≤ 2 * ((((n + 2) : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + (((n + 2) / 4 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ)
        + (((n + 2) / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + (((n + 2) : ℚ) / 2 - 1) * (ModularCurve.cuspCount N : ℚ)) := by sorry
