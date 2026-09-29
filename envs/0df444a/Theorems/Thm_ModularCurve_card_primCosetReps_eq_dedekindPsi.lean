-- Prove2me | Theorems.Thm_ModularCurve_card_primCosetReps_eq_dedekindPsi
-- name    : ModularCurve.card_primCosetReps_eq_dedekindPsi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/71ea1e1d-abc7-5b9b-9316-970bd43e0ef0
-- title:
--   Primitive coset representatives are counted by Dedekind's ψ
-- statement:
--   Let $N$ be a natural number with $N \neq 0$. Consider the finite set [`ModularCurve.primCosetReps N`](def/ModularCurve_PrimCosetReps.html#L8) of triples $(a,b,d)$ of natural numbers, each of its three entries lying in $\{0,1,\dots,N\}$, subject to the conditions $a\cdot d = N$, $b < d$, and $\gcd(a,\gcd(b,d)) = 1$. The theorem asserts that the cardinality of this set equals [`ModularCurve.dedekindPsi N`](def/ModularCurve_X0.html#L201), defined as the sum $\sum_{e \mid N,\ e \text{ squarefree}} N/e$, the quotients being taken in the natural numbers and the sum ranging over the squarefree divisors $e$ of $N$. In other words, the number of triples $(a,b,d)$ with $ad = N$, $0 \le b < d$ and $a$, $b$, $d$ jointly coprime is Dedekind's $\psi(N) = N\prod_{p \mid N}(1 + 1/p)$, here presented in the equivalent form of a sum over squarefree divisors. The bound that each coordinate be at most $N$ is harmless, since $ad = N$ and $N \neq 0$ already force $a \le N$ and $d \le N$, whence $b < d \le N$.
--
--   The triples counted here are the standard representatives for the right cosets of $\Gamma_0(N)$-type matrices of determinant $N$, and $\psi(N) = [\mathrm{SL}_2(\mathbb{Z}):\Gamma_0(N)]$ is the degree in $Y$ of the modular polynomial $\Phi_N(X,Y)$. The count is the combinatorial input for the coset factorisation $\Phi_N(j(\tau)^{\,\cdot},Y) = \prod (Y - j((a\tau+b)/d))$, and it is used in the degree and separability statements for modular polynomial data, namely [`ModularCurve.ModularPolynomialData.map_adjoin_jqNModC_eq_cosetTwoVarPoly`](thm.html#ModularCurve.ModularPolynomialData.map_adjoin_jqNModC_eq_cosetTwoVarPoly), [`ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero`](thm.html#ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero) and [`ModularCurve.valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf`](thm.html#ModularCurve.valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.card_primCosetReps_eq_dedekindPsi (N : ℕ) (hN : N ≠ 0) :
    (ModularCurve.primCosetReps N).card = ModularCurve.dedekindPsi N := by sorry
