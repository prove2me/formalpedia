-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_variableChange_tateBase_mem_laurentBaseChange_and_cuspData_mem
-- name    : ModularCurve.FullLevel.exists_variableChange_tateBase_mem_laurentBaseChange_and_cuspData_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/f86314ef-c59f-5225-a1d3-0ec25ff058f4
-- title:
--   Tate model and division values over the full-level q-expansion field
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $M'$ be a nonzero natural number not divisible by $q$, and let $\ell$ be a prime with $\ell\ge 3$, $\ell\ne q$ and $\ell\nmid M'$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, let $\zeta\in L$ be a primitive $q$-th root of unity and $\xi\in L$ a primitive $(q\ell)$-th root of unity. Let $K$ be the intermediate field of $L\subseteq L(\!(\mathsf{q})\!)$ obtained as `laurentBaseChange`: the subfield generated over $L$ by the coefficientwise image of the $q$-expansion function field `xHFunctionField` of level $(q\ell)^2M'$ for the subgroup $H$ of $(\mathbb{Z}/(q\ell)^2M')^\times$ consisting of the units congruent to $1$ modulo $q\ell$ (the kernel of reduction to $(\mathbb{Z}/q\ell)^\times$). Then there is a Weierstrass variable change $C$ over $L(\!(\mathsf{q})\!)$ such that all five coefficients $a_1,a_2,a_3,a_4,a_6$ of $C\bullet$`tateBase L (q*ℓ)` — the universal Tate curve with $\mathsf{q}$ substituted by $\mathsf{q}^{q\ell}$ — lie in $K$, and such that for all $v,w\in(\mathbb{Z}/q\ell)^2$ with $v\ne 0$ and $w\ne 0$ the coordinates $x_P=u^{-2}(x-r)$ and $y_P=u^{-3}(y-s(x-r)-t)$ of the $C$-transform of `cuspData L (q*ℓ)` at $(\xi,v,w)$ lie in $K$, where $(x,y)$ is the cusp point attached to $v$ (the toric point when $v_1=0$, otherwise the non-toric point). Only the $P$-coordinates, built from $v$, are constrained; $w$ enters the conclusion only through the data.
--
--   This records that, after one change of variables over the Laurent series field, the Tate curve of level $q\ell$ and its $(q\ell)$-division values at nonzero indices are defined over the full-level $q$-expansion field $K$, the function-field incarnation of the modular curve for units congruent to $1$ modulo $q\ell$. It is used in the identification of $j$-invariants of points of the base-changed curve with values $j(\mathsf{q}^N)$ under $\Gamma_0$-type operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_variableChange_tateBase_mem_laurentBaseChange_and_cuspData_mem.lean

import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_variableChange_tateBase_mem_laurentBaseChange_and_cuspData_mem
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries L),
      (C • ModularCurve.tateBase L (q * ℓ)).a₁ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₂ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₃ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₄ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₆ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      ∀ v w : Fin 2 → ZMod (q * ℓ), v ≠ 0 → w ≠ 0 →
        ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v w).variableChange C).xP ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
        ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v w).variableChange C).yP ∈ Set.range ((↑) : ↥K → LaurentSeries L) := by sorry
