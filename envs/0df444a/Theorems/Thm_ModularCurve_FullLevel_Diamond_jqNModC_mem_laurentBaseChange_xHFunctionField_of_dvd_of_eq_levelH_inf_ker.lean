-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_jqNModC_mem_laurentBaseChange_xHFunctionField_of_dvd_of_eq_levelH_inf_ker
-- name    : ModularCurve.FullLevel.Diamond.jqNModC_mem_laurentBaseChange_xHFunctionField_of_dvd_of_eq_levelH_inf_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/5ac88189-b38e-54e5-a4ef-ad56b8344405
-- title:
--   j(q^N) lies in the H₁-level field for N ∣ q²M'
-- statement:
--   Let $q$ be a prime, let $M' \ge 1$, let $\ell_g$ be a divisor of $M'$, and let $L$ be a field of characteristic zero. Let $H_1$ be a subgroup of $(\mathbb{Z}/q^2M')^\times$ assumed equal to the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, with the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell_g)^\times$ attached to the divisibility $\ell_g \mid q^2M'$ coming from $\ell_g \mid M'$. Let $N \ge 1$ divide $q^2M'$. The conclusion is that [`ModularCurve.jqNModC L N`](def/ModularCurve_JqCoeff.html#L18), namely the image of the Laurent series $\mathfrak q^{-1}\cdot(\text{the } j\text{-numerator power series over } L)$ under the exponent-scaling ring homomorphism [`ModularCurve.qExpand L N`](def/ModularCurve_X0.html#L25) (the substitution $\mathfrak q \mapsto \mathfrak q^N$), belongs to [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q^2*M') H₁)`](def/ModularCurve_LaurentCoeff.html#L103): the intermediate field of $L(\!(\mathfrak q)\!)$ generated over $L$ by the coefficientwise image, under $\mathbb{Q} \to L$, of the rational $\mathfrak q$-expansion function field `xHFunctionFieldC ℚ (q^2*M') H₁` of the modular curve of level $(q^2M', H_1)$.
--
--   This is the statement that $j(N\tau)$, as a $\mathfrak q$-expansion, is a function on the modular curve of level $(q^2M', H_1)$ whenever $N \mid q^2M'$, in the form needed at the auxiliary full level with $H_1$ cut out by the two congruence conditions modulo $q$ and modulo $\ell_g$. It is used in the analysis of the diamond action on Tate points and cyclic quotients at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_jqNModC_mem_laurentBaseChange_xHFunctionField_of_dvd_of_eq_levelH_inf_ker.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.FullLevel.Diamond.jqNModC_mem_laurentBaseChange_xHFunctionField_of_dvd_of_eq_levelH_inf_ker
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (ℓg : ℕ) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (N : ℕ) [NeZero N] (hN : N ∣ q ^ 2 * M') :
    ModularCurve.jqNModC L N ∈
      ModularCurve.laurentBaseChange L
        (ModularCurve.xHFunctionField (q ^ 2 * M') H₁) := by sorry
