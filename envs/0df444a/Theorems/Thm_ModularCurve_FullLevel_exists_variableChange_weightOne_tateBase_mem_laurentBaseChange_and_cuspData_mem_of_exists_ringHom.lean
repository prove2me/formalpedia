-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom
-- name    : ModularCurve.FullLevel.exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/fe57b8a4-ffb3-52de-84ae-a774e13bd20a
-- title:
--   Weight-one change of variables: Tate curve and cusps over K
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $M'$ be a non-zero natural number with $q\nmid M'$, and let $\ell$ be a prime with $\ell\ge 3$, $\ell\ne q$ and $\ell\nmid M'$. Let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $(q\ell)$-th root of unity, and assume there is a ring homomorphism $\iota:L\to\mathbb{C}$ with $\iota(\xi)=e^{2\pi i/(q\ell)}$. Let $K$ be the intermediate field of $L\subseteq L((\mathsf q))$ equal to `laurentBaseChange`, i.e. generated over $L$ by the coefficientwise image under $\mathbb{Q}\to L$ of the $q$-expansion function field `xHFunctionField` of level $(q\ell)^2M'$ for the subgroup $H=\ker\big((\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times\big)$ of units congruent to $1$ modulo $q\ell$. Write $\zeta$ for the unit of $L$ determined by $\xi$ and $(x_0,y_0)=$ `cuspPoint L (q*ℓ) ζ ![1,0]`, which, the second coordinate of the index vanishing, is the toric Tate point `tateToricPoint` at $\zeta$. Then there exists a Weierstrass variable change $C=\langle u,r,s,t\rangle$ over $L((\mathsf q))$ with $u\,(2x_0+1/6)=2y_0+x_0$ and $r=-1/12$, $s=-1/2$, $t=1/24$ (constant Laurent series), such that the five coefficients $a_1,a_2,a_3,a_4,a_6$ of $C\cdot$ `tateBase L (q*ℓ)` (the Tate curve with parameter substituted by $\mathsf q^{q\ell}$) all lie in $K$, and such that for all non-zero $v,w:\mathrm{Fin}\,2\to\mathbb{Z}/q\ell$ the coordinates $x_P,y_P$ of the $C$-transform of `cuspData L (q*ℓ) ζ v w`, namely $u^{-2}(x_v-r)$ and $u^{-3}(y_v-s(x_v-r)-t)$ for the cusp point indexed by $v$, lie in $K$.
--
--   This provides the twisted Weierstrass model of the Tate curve over the function field of $X_H$ of level $(q\ell)^2M'$, together with the $K$-rationality of its $(q\ell)$-torsion cusp coordinates, in the normalisation $r=-1/12$, $s=-1/2$, $t=1/24$ fixed by the weight-one unit at the toric index $(1,0)$. It feeds the construction of level automorphisms and of the rigidified $\Gamma_0$-type data at the cusps in the $\Gamma_0(q^2)$-tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom.lean

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

theorem ModularCurve.FullLevel.exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries L),

      ((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) *
          (2 * (ModularCurve.cuspPoint L (q * ℓ)
            (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 +
            HahnSeries.C ((6 : L)⁻¹)) =
        2 * (ModularCurve.cuspPoint L (q * ℓ)
            (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 +
          (ModularCurve.cuspPoint L (q * ℓ)
            (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
      C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹) ∧

      (C • ModularCurve.tateBase L (q * ℓ)).a₁ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₂ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₃ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₄ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₆ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      ∀ v w : Fin 2 → ZMod (q * ℓ), v ≠ 0 → w ≠ 0 →
        ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v w).variableChange C).xP ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
        ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v w).variableChange C).yP ∈ Set.range ((↑) : ↥K → LaurentSeries L) := by sorry
