-- Prove2me | Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
-- name    : ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/e1e4047a-27d8-5d03-8987-2e97cdbcffa3
-- title:
--   The q-expansion function field over ℚ is a one-variable function field
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of finite index containing the translation matrix $T = \begin{pmatrix}1&1\\0&1\end{pmatrix}$ (`ModularGroup.T`). Consider the intermediate field [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101) of the field of formal Laurent series over $\mathbb{Q}$: by definition it is the subfield generated over $\mathbb{Q}$ by the set `intFormRatiosC`, consisting of those Laurent series of the form `intSeriesC ℚ pf / intSeriesC ℚ pg`, where for some weight $k \in \mathbb{Z}$ there are modular forms $f, g$ of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$ and power series $pf, pg$ with integer coefficients satisfying the predicates `IsIntegralQExp f pf` and `IsIntegralQExp g pg`, with `intSeriesC ℚ pg` nonzero; here `intSeriesC ℚ p` denotes the Laurent series over $\mathbb{Q}$ attached to an integral power series $p$. The theorem asserts that this field contains an element $x$ which is transcendental over $\mathbb{Q}$ and for which the whole field is finite-dimensional as a vector space over the intermediate field $\mathbb{Q}(x)$ obtained by adjoining $x$ to $\mathbb{Q}$ inside it. No particular such $x$, and no bound on the degree, is asserted.
--
--   This is the basic finiteness statement making the $q$-expansion presentation of the modular curve attached to $\Gamma$ into an algebraic function field of one variable over $\mathbb{Q}$, in the classical form obtained from $j$ (or $E_6^2/E_4^3$) together with the finiteness of the index of $\Gamma$. It is the hypothesis under which the general theory of one-variable function fields (places, divisor classes, genus, torsion in $\mathrm{Pic}^0$) is applied to these fields, and is used by the corresponding statement after base change of the coefficient field and in the construction of smooth proper models of modular curves with their Galois-compatible structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) :
    ∃ x : ModularCurve.qExpFunctionFieldC ℚ Γ, Transcendental ℚ x ∧
      FiniteDimensional
        (IntermediateField.adjoin ℚ ({x} : Set (ModularCurve.qExpFunctionFieldC ℚ Γ)))
        (ModularCurve.qExpFunctionFieldC ℚ Γ) := by sorry
