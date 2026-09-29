-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_chart_dichotomy_jBar
-- name    : ModularCurve.CharPModel.chart_dichotomy_jBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/9f44473d-b005-52fe-b6aa-ca64381aa52b
-- title:
--   Chart dichotomy for places of the modular function field
-- statement:
--   Let $N$ be a nonzero natural number and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ (the Lean `AlgebraicClosure ℚ`). Write $F_N =$ `modularFunctionFieldFull N` for the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the series $j(q^d)$ for the nonzero divisors $d \mid N$, and let $E_N =$ `laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)` be the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the images of $F_N$ under the coefficientwise embedding `coeffEmb`. Assume given, for every nonzero $d$ dividing $N$, a datum `ModularPolynomialData d`: a polynomial $\Phi \in (\mathbb{Z}[Y])[X]$ which is monic, of degree $\psi(d) = \sum_{e \mid d,\ e \text{ squarefree}} d/e$ in $X$, and which vanishes when $X$ is specialised to $j(q^d)$ and the coefficients are evaluated at $j(q)$. Let $w$ be a place of $E_N$ over $\overline{\mathbb{Q}}$ in the sense of the project structure `Place`: a valuation subring of $E_N$, not equal to all of $E_N$, containing the image of $\overline{\mathbb{Q}}$, and a principal ideal ring. Let $\bar{j} =$ `jBar N` be the element of $E_N$ given by the $q$-expansion of $j$ with coefficients embedded into $\overline{\mathbb{Q}}$. Then one of the following holds: there is $a \in A$ with $\bar{j} - a$ in `w.toValuationSubring.nonunits`, the non-units of the valuation ring at $w$ (its maximal ideal); or there is $a \in A$ with $\bar{j}^{-1} - a$ in that same set.
--
--   This is the standard finite-versus-polar chart alternative for the $j$-line: every place of the level-$N$ modular function field in characteristic zero either has $j$ regular with residue the reduction of a constant in $A$, or has $1/j$ regular with such a residue (the pole of $j$ corresponding to the constant $0$). It is the input used to locate places on one of the two charts when constructing the characteristic-$p$ fibre model, and is cited by the lemmas identifying poles of $j$ and of $j_N$ at the specialised places and by the computations of their dictionary values.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_chart_dichotomy_jBar.lean

import Definitions.Def_ModularCurve_FibreModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.CharPModel.chart_dichotomy_jBar (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (w : Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) :
    (∃ a : A, (jBar N - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        (a : AlgebraicClosure ℚ)) ∈ w.toValuationSubring.nonunits) ∨
      (∃ a : A, ((jBar N)⁻¹ - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        (a : AlgebraicClosure ℚ)) ∈ w.toValuationSubring.nonunits) := by sorry
