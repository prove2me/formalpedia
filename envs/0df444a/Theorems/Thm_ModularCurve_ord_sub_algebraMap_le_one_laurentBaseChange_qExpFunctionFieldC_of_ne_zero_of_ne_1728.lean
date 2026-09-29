-- Prove2me | Theorems.Thm_ModularCurve_ord_sub_algebraMap_le_one_laurentBaseChange_qExpFunctionFieldC_of_ne_zero_of_ne_1728
-- name    : ModularCurve.ord_sub_algebraMap_le_one_laurentBaseChange_qExpFunctionFieldC_of_ne_zero_of_ne_1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/a6de7247-5400-574b-aa68-d302fb996ed0
-- title:
--   Zeros of j-a are simple for a≠ 0,1728
-- statement:
--   Fix $M \geq 1$ and a subgroup $\Gamma$ of $\mathrm{SL}(2,\mathbb{Z})$ containing $\Gamma_1(M)$. Let $F_0 =$ `qExpFunctionFieldC ℚ Γ` be the intermediate field of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the set of quotients `intSeriesC ℚ pf / intSeriesC ℚ pg`, where $f,g$ are modular forms of one and the same weight $k$ for $\Gamma$ (viewed in $\mathrm{GL}(2,\mathbb{R})$), $p_f,p_g$ are power series over $\mathbb{Z}$ with `IsIntegralQExp f pf` and `IsIntegralQExp g pg`, and `intSeriesC ℚ pg ≠ 0`; and let $F =$ `laurentBaseChange ℂ F₀` be the intermediate field of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the image of $F_0$ under coefficientwise extension of scalars $\mathbb{Q} \to \mathbb{C}$. Let $y \in F$ be an element whose underlying Laurent series is `jqModC ℂ`, that is $q^{-1}$ times the image over $\mathbb{C}$ of the power series `jNum` $= E_4^3 \cdot$ `dedekindEtaUnitInv`, the $q$-expansion of the modular invariant $j$. Let $a \in \mathbb{C}$ with $a \neq 0$ and $a \neq 1728$, and let $P$ be a place of $F$ over $\mathbb{C}$, i.e. a valuation subring of $F$ other than $F$ itself which contains the image of $\mathbb{C}$ and is a principal ideal ring. Then $\mathrm{ord}_P(y - a) \leq 1$, where $\mathrm{ord}_P$ is minus the logarithm of the associated adic valuation.
--
--   This is the local content of the Riemann–Hurwitz computation for modular curves: the covering $X(\Gamma) \to X(1)$ given by $j$ is unramified over every finite value $a \notin \{0,1728\}$, so that each zero of $j-a$ on the curve with function field $F$ is simple. It feeds, together with the companion bounds at $j=0$ and $j=1728$, into the ramification count over an algebraic closure and into the genus inequality for $\Gamma \supseteq \Gamma_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_sub_algebraMap_le_one_laurentBaseChange_qExpFunctionFieldC_of_ne_zero_of_ne_1728.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.ord_sub_algebraMap_le_one_laurentBaseChange_qExpFunctionFieldC_of_ne_zero_of_ne_1728
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (a : ℂ) (ha₀ : a ≠ 0) (ha₁₇₂₈ : a ≠ 1728)
    (P : AlgebraicCurve.Place ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ))) :
    P.ord (y - algebraMap ℂ
        (ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) a) ≤ 1 := by sorry
