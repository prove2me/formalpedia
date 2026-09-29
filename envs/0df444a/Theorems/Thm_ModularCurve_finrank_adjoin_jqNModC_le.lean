-- Prove2me | Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_le
-- name    : ModularCurve.finrank_adjoin_jqNModC_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/d940315e-95eb-54d9-9321-fd3a6ae7fd67
-- title:
--   Degree bound ψ(N) for K(j)(j(q^N)) over K(j)
-- statement:
--   Let $K$ be a field and let $N$ be a nonzero natural number. Inside the field of Laurent series $K((q))$ consider the two elements $j =$ `jqModC K`, namely $q^{-1}$ times the image in $K$ of the integral power series `jNum` $= E_4^3\cdot$`dedekindEtaUnitInv`, and $j_N =$ `jqNModC K N`, the image of $j$ under the ring homomorphism `qExpand K N` which multiplies all Hahn-series exponents by $N$ (substitution $q \mapsto q^N$). Assume given a term `data` of the structure `ModularPolynomialData N`, that is, a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ which is monic in $Y$, has $Y$-degree equal to $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, and satisfies $\Phi = 0$ after evaluating its coefficients by `evalAtJ` (the $\mathbb{Z}$-algebra map $\mathbb{Z}[X] \to \mathbb{Q}((q))$ sending $X$ to the rational $q$-expansion of $j$) and substituting $Y \mapsto$ `jqN N`. The conclusion is the inequality $$[E(j_N) : E] \le \psi(N),$$ where $E = K(j)$ is the intermediate field of $K((q))$ generated over $K$ by $j$ and $E(j_N)$ is the intermediate field of $K((q))$ generated over $E$ by $j_N$, the left-hand side being `Module.finrank`.
--
--   This is the upper bound $[K(j)(j(q^N)) : K(j)] \le \psi(N)$ for the modular function field of $X_0(N)$ over an arbitrary field $K$, obtained from a modular polynomial packet by specialisation of coefficients; no irreducibility of $\Phi$ and no hypothesis on the characteristic of $K$ enter. Since `Module.finrank` vanishes for infinite-dimensional extensions, the inequality is read together with the companion statement [`ModularCurve.finiteDimensional_adjoin_jqNModC`](thm.html#ModularCurve.finiteDimensional_adjoin_jqNModC); both feed the analysis of the function field of $X_0(N)$ and of its cusps, e.g. [`ModularCurve.coeffMap_mem_modularFunctionFieldC`](thm.html#ModularCurve.coeffMap_mem_modularFunctionFieldC) and the uniqueness statements for the places at the cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_adjoin_jqNModC_le.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.finrank_adjoin_jqNModC_le (K : Type*) [Field K] {N : ℕ} [NeZero N] (data : ModularPolynomialData N) : Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) ({jqNModC K N} : Set (LaurentSeries K))) ≤ dedekindPsi N := by sorry
