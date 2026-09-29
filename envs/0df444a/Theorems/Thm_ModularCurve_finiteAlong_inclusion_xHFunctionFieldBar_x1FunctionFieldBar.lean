-- Prove2me | Theorems.Thm_ModularCurve_finiteAlong_inclusion_xHFunctionFieldBar_x1FunctionFieldBar
-- name    : ModularCurve.finiteAlong_inclusion_xHFunctionFieldBar_x1FunctionFieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/a8abe178-97a5-5769-90a7-0ebfad8cf516
-- title:
--   Finiteness of ℚ̄-function field of X₁(M) over that of X_H(M)
-- statement:
--   Let $M$ be a nonzero natural number and let $H$ be a subgroup of $(\mathbb Z/M)^\times$. Inside the Laurent series field $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ consider the two intermediate fields over $\overline{\mathbb Q}$ obtained by base change from the rational $q$-expansion function fields: [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123) is the subfield of $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of [`ModularCurve.xHFunctionFieldC ℚ M H`](def/ModularCurve_XH.html#L76), and [`ModularCurve.x1FunctionFieldBar M`](def/ModularCurve_X1.html#L182) is the subfield generated over $\overline{\mathbb Q}$ by the coefficientwise image of [`ModularCurve.x1FunctionFieldC ℚ M`](def/ModularCurve_X1.html#L134). Assume the hypothesis `hle` that the first is contained in the second. The conclusion is [`AlgebraicCurve.FiniteAlong`](def/AlgebraicCurve_Correspondence.html#L37) for the inclusion algebra homomorphism `IntermediateField.inclusion hle`, that is: when [`ModularCurve.x1FunctionFieldBar M`](def/ModularCurve_X1.html#L182) is regarded as an algebra over [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123) via that inclusion, it is a finite module, i.e. the field extension $\overline{\mathbb Q}F(\Gamma_H(M))\subseteq\overline{\mathbb Q}F(\Gamma_1(M))$ is finite. No numerical value for the degree is asserted.
--
--   This is the finiteness of the level-$H$ tower step for function fields of modular curves over $\overline{\mathbb Q}$: classically the degree equals $[\Gamma_H(M):\pm\Gamma_1(M)]$, but only finiteness is recorded here. It underlies the degeneracy and pullback/pushforward maps between the Jacobians of $X_1(M)$ and $X_H(M)$, and is cited in the construction of the associated maps on Tate modules and Weil pairings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteAlong_inclusion_xHFunctionFieldBar_x1FunctionFieldBar.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.finiteAlong_inclusion_xHFunctionFieldBar_x1FunctionFieldBar
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hle : ModularCurve.xHFunctionFieldBar M H ≤ ModularCurve.x1FunctionFieldBar M) :
    AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) (IntermediateField.inclusion hle) := by sorry
