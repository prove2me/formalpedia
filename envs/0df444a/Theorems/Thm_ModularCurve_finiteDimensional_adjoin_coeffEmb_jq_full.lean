-- Prove2me | Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
-- name    : ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/7ced3fad-1396-570b-88c4-c0308909da0f
-- title:
--   Finiteness of the base-changed level-N function field over L(j)
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure and let $N$ be a natural number with $N \neq 0$. Inside $\mathrm{LaurentSeries}\,\mathbb{Q}$ let $\mathtt{jq}$ be the Laurent series $q^{-1}$ times the image of the integral power series $\mathtt{jNum}$ under $\mathbb{Z} \to \mathbb{Q}$ (the $q$-expansion of the $j$-invariant), and let $\mathtt{modularFunctionFieldFull}\ N$ be the intermediate field of $\mathrm{LaurentSeries}\,\mathbb{Q}$ obtained by adjoining to $\mathbb{Q}$ all the expansions $\mathtt{qExpand}\ \mathbb{Q}\ d\ \mathtt{jq}$ for nonzero divisors $d$ of $N$. Let $\mathtt{coeffEmb}\ L$ be the ring embedding $\mathrm{LaurentSeries}\,\mathbb{Q} \to \mathrm{LaurentSeries}\,L$ acting on coefficients through $\mathbb{Q} \to L$, and let $E = \mathtt{laurentBaseChange}\ L\ (\mathtt{modularFunctionFieldFull}\ N)$ be the intermediate field of $\mathrm{LaurentSeries}\,L$ generated over $L$ by the image of $\mathtt{modularFunctionFieldFull}\ N$ under this embedding. The element $\mathtt{coeffEmb}\ L\ \mathtt{jq}$ lies in $E$, and the assertion is that $E$ is finite-dimensional as a vector space over the intermediate field of $E$ generated over $L$ by that single element. Only finiteness is asserted, not the value of the degree.
--
--   This is the statement that the function field of $X_0(N)$, realised as a field of formal $q$-expansions with coefficients extended from $\mathbb{Q}$ to an arbitrary field $L$ of characteristic zero, is a finite extension of $L(j)$; taking $L = \overline{\mathbb{Q}}$ or $L = \mathbb{C}$ gives the cases used later. It underlies the separability statement proved alongside it and is invoked throughout the $q$-expansion model of $X_0(N)$, where finiteness over $L(j)$ is what makes orders of differentials, place-reduction dictionaries and residue computations available.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full.lean

import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] : FiniteDimensional (IntermediateField.adjoin L ({⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩} : Set (laurentBaseChange L (modularFunctionFieldFull N)))) (laurentBaseChange L (modularFunctionFieldFull N)) := by sorry
