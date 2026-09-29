-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_prime_level
-- name    : ModularCurve.FullLevel.exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_prime_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/3cab98b8-44d7-5e42-a970-9563bddedae5
-- title:
--   Weight-one twist of Tate(mathsf q^ℓ) rational over level ℓ²M'
-- statement:
--   Fix a natural number $M'\neq 0$ and a prime $\ell\geq 3$ with $\ell\nmid M'$, a field $L$ of characteristic zero, and $\zeta\in L$ a primitive $\ell$-th root of unity admitting a ring homomorphism $\iota:L\to\mathbb C$ with $\iota(\zeta)=e^{2\pi i/\ell}$. Let $K$ be the intermediate field of $L\subset L((\mathsf q))$ obtained as `laurentBaseChange` of the $\mathsf q$-expansion function field `xHFunctionField (ℓ ^ 2 * M') (levelH ℓ M')`, that is, the subfield of `LaurentSeries L` generated over $L$ by the coefficientwise images under $\mathbb Q\to L$ of that rational function field, where `levelH ℓ M'` is the kernel of the `ZMod.unitsMap` reduction of $(\mathbb Z/\ell^2M')^\times$ attached to the divisibility `dvd_sq_mul ℓ M'`. Then there is a Weierstrass variable change $C=(u,r,s,t)$ over $L((\mathsf q))$ such that, writing $(x,y)$ for `cuspPoint L ℓ ζ ![1, 0]` (here the second coordinate of the vector vanishes, so this is the Tate toric point at parameter $\zeta$), one has $u\,(2x+\tfrac16)=2y+x$, and $r=-\tfrac1{12}$, $s=-\tfrac12$, $t=\tfrac1{24}$ as constant Laurent series; all five coefficients $a_1,a_2,a_3,a_4,a_6$ of $C\bullet$ `tateBase L ℓ`, the Tate curve with $\mathsf q$ replaced by $\mathsf q^{\ell}$, lie in $K$; and for all nonzero $v,w\in(\mathbb Z/\ell)^2$ the coordinates $u^{-2}(x_v-r)$ and $u^{-3}(y_v-s(x_v-r)-t)$ of the $P$-part of `(cuspData L ℓ ζ v w).variableChange C` lie in $K$ (these depend only on $v$, through `cuspPoint L ℓ ζ v`, so the quantifier over $w$ carries no extra content).
--
--   This records the rationality, over the function field of $X_H(\ell^2M')$ base-changed to $L$, of the weight-one twist of the Tate curve $\mathrm{Tate}(\mathsf q^{\ell})$ normalised at the toric cusp point with parameter $\zeta$, together with the $\mathsf q$-expansions of the $\ell$-torsion cusp points in that model. It feeds the construction of étale full-level models at level $\ell$, being used by [`ModularCurve.FullLevel.exists_variableChange_raw_etale_tate_weightOne_level_fst_gamma0Pow`](thm.html#ModularCurve.FullLevel.exists_variableChange_raw_etale_tate_weightOne_level_fst_gamma0Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_prime_level.lean

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

theorem ModularCurve.FullLevel.exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_prime_level
    (M' : ℕ) [NeZero M']
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ ℓ)
    (hιζ : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (ℓ ^ 2 * M')
        (ModularCurve.FullLevel.levelH ℓ M'))) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries L),

      ((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) *
          (2 * (ModularCurve.cuspPoint L ℓ
            (hζ.isUnit (Fact.out : ℓ.Prime).ne_zero).unit ![1, 0]).1 +
            HahnSeries.C ((6 : L)⁻¹)) =
        2 * (ModularCurve.cuspPoint L ℓ
            (hζ.isUnit (Fact.out : ℓ.Prime).ne_zero).unit ![1, 0]).2 +
          (ModularCurve.cuspPoint L ℓ
            (hζ.isUnit (Fact.out : ℓ.Prime).ne_zero).unit ![1, 0]).1 ∧
      C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹) ∧

      (C • ModularCurve.tateBase L ℓ).a₁ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L ℓ).a₂ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L ℓ).a₃ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L ℓ).a₄ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L ℓ).a₆ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      ∀ v w : Fin 2 → ZMod ℓ, v ≠ 0 → w ≠ 0 →
        ((ModularCurve.cuspData L ℓ (hζ.isUnit (Fact.out : ℓ.Prime).ne_zero).unit v w).variableChange C).xP ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
        ((ModularCurve.cuspData L ℓ (hζ.isUnit (Fact.out : ℓ.Prime).ne_zero).unit v w).variableChange C).yP ∈ Set.range ((↑) : ↥K → LaurentSeries L) := by sorry
