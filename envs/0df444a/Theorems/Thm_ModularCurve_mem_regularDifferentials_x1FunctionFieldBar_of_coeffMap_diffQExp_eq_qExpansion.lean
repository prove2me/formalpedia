-- Prove2me | Theorems.Thm_ModularCurve_mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion
-- name    : ModularCurve.mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/7f1fc8a8-c9d6-5903-9402-029402bf82fc
-- title:
--   Differentials with cusp-form q-expansion are regular
-- statement:
--   Let $M$ be a non-zero natural number, let $\iota_0 : \overline{\mathbb Q} \to \mathbb C$ be a ring homomorphism from `AlgebraicClosure ℚ` to $\mathbb C$, and let $f$ be a cusp form of weight $2$ for $\Gamma_1(M)$. Write $F =$ `x1FunctionFieldBar M` for the intermediate field of $\overline{\mathbb Q}((q))$ over $\overline{\mathbb Q}$ obtained as `laurentBaseChange`, i.e. generated over $\overline{\mathbb Q}$ by the coefficientwise image of the function field `x1FunctionField M` $\subseteq \mathbb Q((q))$. Let $\omega \in \Omega_{F/\overline{\mathbb Q}}$ be a Kähler differential, and assume that applying $\iota_0$ to each Laurent coefficient of `diffQExp F ω` — the image of $\omega$ under the $F$-linear map lifting to $\Omega_{F/\overline{\mathbb Q}}$ the derivation `qEuler` of $\overline{\mathbb Q}((q))$ (multiplication of the $n$-th coefficient by $n$, that is $q\,\mathrm d/\mathrm dq$) restricted along $F \hookrightarrow \overline{\mathbb Q}((q))$ — yields the Laurent series attached to the power series `qExpansion 1 f`. The conclusion is that $\omega$ belongs to `regularDifferentials`, the $\overline{\mathbb Q}$-submodule of those $\eta$ such that for every place $v$ of $F/\overline{\mathbb Q}$ (a valuation subring of $F$, containing the image of $\overline{\mathbb Q}$, not equal to $F$, and a principal ideal ring) there is some $g$ in that valuation subring with $\eta = g \cdot \mathrm d(\pi_v)$, $\pi_v$ a uniformiser of $v$.
--
--   This is one half of the classical identification of weight-$2$ cusp forms on $\Gamma_1(M)$ with regular differentials on the curve $X_1(M)$: a differential whose $q$-expansion, under the $q\,\mathrm d/\mathrm dq$ pairing, is the $q$-expansion of a cusp form has no poles at any place of the function field. It feeds the construction of the isomorphism between the space of cusp forms and the regular differentials, [`ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm`](thm.html#ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_AlgebraicCurve_RegularDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem ModularCurve.mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion
    (M : ℕ) [NeZero M] (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2)
    (ω : Ω[↥(ModularCurve.x1FunctionFieldBar M)⁄AlgebraicClosure ℚ])
    (hω : ModularCurve.coeffMap ι₀ (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M) ω) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f)) :
    ω ∈ AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) := by sorry
