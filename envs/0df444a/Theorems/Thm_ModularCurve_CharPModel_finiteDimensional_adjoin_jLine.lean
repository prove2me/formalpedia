-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine
-- name    : ModularCurve.CharPModel.finiteDimensional_adjoin_jLine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/82e95414-ff00-5c33-8876-a037f534bbc7
-- title:
--   Finite dimensionality of C_k(N) over k(jmath̃)
-- statement:
--   Let $k$ be a field and $N$ a nonzero natural number, and let `data` be modular polynomial data of level $N$: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ which is monic, has degree $\sum_{d \mid N,\ d \text{ squarefree}} N/d$ in $Y$, and satisfies $\Phi(\jmath, \jmath_N) = 0$, where the coefficients in $\mathbb{Z}[X]$ are evaluated at the $q$-expansion `jq` and $Y$ at its level-$N$ companion `jqN N`, inside the Laurent series over $\mathbb{Q}$. Inside the field of Laurent series over $k$, consider the element $\tilde\jmath =$ `jqModC k`, namely $q^{-1}$ times the power series obtained from `jNum` $= E_4^3 \cdot$ `dedekindEtaUnitInv` by reducing its integer coefficients into $k$, and its image $\tilde\jmath_N$ under the substitution `qExpand k N`. Let `modularFunctionFieldC k N` be the intermediate field $k(\tilde\jmath, \tilde\jmath_N)$ generated over $k$ by these two Laurent series. The assertion is that `modularFunctionFieldC k N` is finite dimensional over the intermediate field of itself obtained by adjoining $\tilde\jmath$ to $k$.
--
--   This is the finiteness of the degree $[C_k(N) : k(\tilde\jmath)]$ for the characteristic-free (Kroneckerian) model of the level-$N$ modular function field realised through $q$-expansions, the second generator being integral of bounded degree over the first by the reduction of the modular polynomial. It supports the results on places, specialisations and widths of the modular curve model, and the computation of orders of Hecke multipliers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine.lean

import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.CharPModel.finiteDimensional_adjoin_jLine (k : Type*) [Field k]
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N) :
    FiniteDimensional
      (IntermediateField.adjoin k
        ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N) := by sorry
