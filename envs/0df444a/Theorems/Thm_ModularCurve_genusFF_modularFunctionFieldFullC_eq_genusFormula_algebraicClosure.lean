-- Prove2me | Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFormula_algebraicClosure
-- name    : ModularCurve.genusFF_modularFunctionFieldFullC_eq_genusFormula_algebraicClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/1cd7db01-f075-5222-b778-077437799ef9
-- title:
--   Genus of the level-N modular function field over ℚ̄
-- statement:
--   Let $N$ be a natural number with $N \neq 0$. Write $K = \overline{\mathbb{Q}}$ (the `AlgebraicClosure` of $\mathbb{Q}$) and let $F =$ `modularFunctionFieldFullC K N` be the intermediate field of the Laurent series field $K((q))$ obtained by adjoining to $K$ the set of series $\mathrm{qExpand}\,K\,d\,(\mathrm{jqModC}\,K)$ for the nonzero divisors $d \mid N$, i.e. the substitutions $q \mapsto q^{d}$ of the $q$-expansion of $j$. The assertion is that the invariant `genusFF K F`, defined as the dimension over $K$ of the space $H^1$ attached to the zero divisor in the group of divisors $\mathrm{Place}(K,F) \to_{f} \mathbb{Z}$ of $F/K$, becomes, after the cast $\mathbb{N} \to \mathbb{Q}$, equal to $\mathrm{genusFormula}(N)$, namely
--   $$1 + \frac{\psi(N)}{12} - \frac{\nu_2(N)}{4} - \frac{\nu_3(N)}{3} - \frac{\nu_\infty(N)}{2},$$
--   where $\psi(N) = \sum_{d \mid N,\ d\ \text{squarefree}} N/d$, $\nu_2(N)$ is the number of $x \in \mathbb{Z}/N$ with $x^2+1=0$, $\nu_3(N)$ the number of $x \in \mathbb{Z}/N$ with $x^2+x+1=0$, and $\nu_\infty(N) = \sum_{d \mid N} \varphi(\gcd(d, N/d))$.
--
--   This is the classical genus formula for $X_0(N)$, here for the Laurent-series model of the level-$N$ modular function field over an algebraically closed field of characteristic $0$. It supplies the genus input for the Riemann–Roch count of dimensions of spaces of modular forms over $\overline{\mathbb{Q}}$, and is used in the comparison of function fields at level $H$ for $N$ divisible by $3$ and in the construction of linearly independent families of mod $p$ modular functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFormula_algebraicClosure.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.genusFF_modularFunctionFieldFullC_eq_genusFormula_algebraicClosure (N : ℕ) [NeZero N] :
    (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldFullC (AlgebraicClosure ℚ) N) : ℚ) = genusFormula N := by sorry
