-- Prove2me | Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_gamma0_le_laurentBaseChange_xHFunctionField
-- name    : ModularCurve.laurentBaseChange_qExpFunctionFieldC_gamma0_le_laurentBaseChange_xHFunctionField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/cd44158d-9aff-5091-a808-23fcd0e0af11
-- title:
--   Base change of the Γ₀(M') q-expansion field lies in X_H(N)
-- statement:
--   Let $L$ be a field of characteristic zero, let $M'$ and $N$ be natural numbers with $M' \mid N$, and let $H$ be a subgroup of $(\mathbb{Z}/N)^\times$. For a congruence subgroup $\Gamma$, $\mathrm{qExpFunctionFieldC}\ \mathbb{Q}\ \Gamma$ denotes the intermediate field of $\mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ the set $\mathrm{intFormRatiosC}\ \mathbb{Q}\ \Gamma$ of all quotients $\mathrm{intSeriesC}\ \mathbb{Q}\ p_f / \mathrm{intSeriesC}\ \mathbb{Q}\ p_g$, where $k$ is an integer, $f$ and $g$ are modular forms of weight $k$ for $\Gamma$ viewed inside $\mathrm{GL}_2(\mathbb{R})$, the integral power series $p_f, p_g \in \mathbb{Z}[[q]]$ are integral $q$-expansions of $f$ and $g$ in the sense of `IsIntegralQExp`, and the Laurent series attached to $p_g$ is nonzero. For an intermediate field $F_0$ of $\mathbb{Q}((q))$, $\mathrm{laurentBaseChange}\ L\ F_0$ is the intermediate field of $L((q))$ generated over $L$ by the image of $F_0$ under the coefficientwise map induced by $\mathbb{Q} \to L$. The assertion is the inclusion of intermediate fields of $L((q))$ over $L$: the base change of the $q$-expansion function field of $\Gamma_0(M')$ is contained in the base change of [`ModularCurve.xHFunctionField N H`](def/ModularCurve_XH.html#L79), i.e. of the $q$-expansion function field over $\mathbb{Q}$ of the group [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133).
--
--   This is the change-of-level inclusion of modular function fields, in the form needed after base change from $\mathbb{Q}$ to an arbitrary field of characteristic zero: level $\Gamma_0(M')$ functions are functions on $X_H(N)$ whenever $M' \mid N$. It is used in the regularity and ramification analysis of fibres of the modular curves $X_H$, where rational functions of small level must be recognised as elements of the larger level field over the relevant constants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_gamma0_le_laurentBaseChange_xHFunctionField.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.laurentBaseChange_qExpFunctionFieldC_gamma0_le_laurentBaseChange_xHFunctionField
    (L : Type) [Field L] [CharZero L] (M' N : ℕ) (hMN : M' ∣ N) (H : Subgroup (ZMod N)ˣ) :
    ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) ≤
      ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField N H) := by sorry
