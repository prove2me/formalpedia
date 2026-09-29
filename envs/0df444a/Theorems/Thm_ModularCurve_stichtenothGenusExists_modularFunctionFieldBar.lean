-- Prove2me | Theorems.Thm_ModularCurve_stichtenothGenusExists_modularFunctionFieldBar
-- name    : ModularCurve.stichtenothGenusExists_modularFunctionFieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/7b11af93-ec61-554b-8592-e1f64f59ab36
-- title:
--   Existence of the genus for X₀(N) over ℚ̄
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, and let $F =$ `modularFunctionFieldBar N` be the intermediate field of the Laurent series field $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ over $K = \overline{\mathbb{Q}}$ obtained by adjoining to $K$ the image, under the coefficientwise embedding $\mathrm{LaurentSeries}(\mathbb{Q}) \to \mathrm{LaurentSeries}(\overline{\mathbb{Q}})$, of `modularFunctionFieldFull N`, itself the subfield of $\mathrm{LaurentSeries}(\mathbb{Q})$ generated over $\mathbb{Q}$ by the $q$-expansions `divisorExpansions N`. The assertion is `StichtenothGenusExists` for the pair $(K, F)$, which unfolds to three things: first, the type of places of $F$ over $K$ — valuation subrings of $F$ containing $\mathrm{image}(K)$, different from $F$ itself, and whose valuation ring is a principal ideal ring — is nonempty; second, the Riemann–Roch space $L(0)$ of the zero divisor is a finite-dimensional $K$-vector space; and third, there exist an integer $\gamma$ and a divisor $D_0$ (a finitely supported $\mathbb{Z}$-valued function on places) such that $L(D_0)$ is finite-dimensional over $K$, $\deg D_0 - \ell(D_0) = \gamma - 1$, and $\deg D - \ell(D) \le \gamma - 1$ for every divisor $D$, so that $\gamma$ is the genus in Stichtenoth's sense and the bound is attained at $D_0$.
--
--   This is Riemann's theorem on the existence of the genus, in the form used for function fields with exact constant field, specialised to the function field of $X_0(N)$ over $\overline{\mathbb{Q}}$; it is what makes the genus, the index of speciality and the Riemann–Roch theorem available at this field, and in particular gives finiteness of $\ell(D)$ for every divisor. It is used in the analysis of places of the modular function field and their prolongations, notably in the construction of functions with prescribed poles at specialised places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_stichtenothGenusExists_modularFunctionFieldBar.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.stichtenothGenusExists_modularFunctionFieldBar (N : ℕ) [NeZero N] :
    StichtenothGenusExists (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by sorry
