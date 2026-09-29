-- Prove2me | Theorems.Thm_ModularCurve_stichtenothGenusExists_modularFunctionFieldC_of_perfectField
-- name    : ModularCurve.stichtenothGenusExists_modularFunctionFieldC_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/5dc883f5-e877-5f86-afbb-74cdcdab24b8
-- title:
--   Existence of the genus for K(j(q),j(q^N)) over a perfect field
-- statement:
--   Let $K$ be a perfect field and let $N$ be a natural number with $N \neq 0$. Inside the field $\mathrm{LaurentSeries}\ K$ of formal Laurent series over $K$, consider the two elements $\verb|jqModC| K = q^{-1}\cdot \iota(\verb|jNum|)$, where $\iota$ applies the canonical map $\mathbb{Z} \to K$ to the coefficients of the integral power series $\verb|jNum|$, and $\verb|jqNModC| K N = \verb|qExpand| K N(\verb|jqModC| K)$, the result of substituting $q \mapsto q^{N}$; let $F = \verb|modularFunctionFieldC| K N$ be the intermediate field of $\mathrm{LaurentSeries}\ K$ obtained by adjoining these two elements to $K$. The assertion is $\verb|StichtenothGenusExists| K F$, that is, the conjunction of three statements: the type $\verb|Place| K F$ of places of $F/K$ — valuation subrings of $F$ containing the image of $K$, different from $F$ itself, and principal ideal rings — is nonempty; the Riemann–Roch space $L(0)$ of the zero divisor is finite-dimensional over $K$; and there exist an integer $\gamma$ and a divisor $D_0$ (a finitely supported $\mathbb{Z}$-valued function on places) such that $L(D_0)$ is finite-dimensional over $K$, $\deg D_0 - \ell(D_0) = \gamma - 1$, and $\deg D - \ell(D) \le \gamma - 1$ for every divisor $D$ of $F/K$.
--
--   This is Riemann's theorem on the existence of the genus, in Stichtenoth's formulation, applied to the function field generated over $K$ by the $q$-expansions of $j(q)$ and $j(q^N)$, the function field of the modular curve of level $N$ in this model. It supplies the genus, and through it the Riemann–Roch machinery and finiteness of all $\ell(D)$, for the later work with differentials and Hecke operators on this field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_stichtenothGenusExists_modularFunctionFieldC_of_perfectField.lean

import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.stichtenothGenusExists_modularFunctionFieldC_of_perfectField (K : Type*) [Field K] [PerfectField K]
    (N : ℕ) [NeZero N] : StichtenothGenusExists K (modularFunctionFieldC K N) := by sorry
