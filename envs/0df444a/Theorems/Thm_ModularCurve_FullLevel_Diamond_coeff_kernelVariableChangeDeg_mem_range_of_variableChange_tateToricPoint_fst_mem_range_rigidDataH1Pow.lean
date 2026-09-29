-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_fst_mem_range_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_fst_mem_range_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/b1364f55-bcda-53c9-a243-21463890544e
-- title:
--   Transported μ_{p^k} kernel has coefficients in the level-H₁ field
-- statement:
--   Let $q$ be a prime, let $M'\ge 1$ with $q\nmid M'$, and let $\ell_g$ be a prime with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $(q\ell_g)$-th root of unity, and suppose some ring homomorphism $L\to\mathbb{C}$ sends $\xi$ to $e^{2\pi i/(q\ell_g)}$. Let $H_1\le(\mathbb{Z}/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb{Z}/q)^\times$ with the kernel of reduction to $(\mathbb{Z}/\ell_g)^\times$, and let $K\subset L((\mathsf q))$ be the intermediate field generated over $L$ by the coefficientwise image of the $q$-expansion function field of level $\Gamma_{H_1}(q^2M')$ in $\mathbb{Q}((\mathsf q))$. Let $p$ be a prime with $p^k\mid M'$ and let $h\in(L((\mathsf q)))[X]$ satisfy: for every field $F'$, every $f:L\to F'$ and every primitive $p^k$-th root of unity $\zeta\in F'$, the coefficientwise image of $h$ equals $\prod_{1\le a\le p^k/2,\;p\nmid a}\bigl(X-x(\zeta^a)\bigr)$, where $x(c)$ is the first component of the explicit Tate-curve toric point series [`ModularCurve.toricPoint`](def/ModularCurve_TateSlots.html#L125) $F'$ $q$ $c$. Let $C$ be a Weierstrass variable change over $L((\mathsf q))$, and assume that the $C$-transports $u^{-2}(x_P-r)$ and $u^{-2}(x_Q-r)$ of the abscissae of the toric points [`ModularCurve.tateToricPoint`](def/ModularCurve_KatzLevelPCusps.html#L20) $L$ $q$ at the units $\xi^q$ and $(\xi^q)^2$ both lie in $K$. Then every coefficient of $\bigl((u^{-1})^{2d}\bigr)\,h\bigl(u^2X+r\bigr)$, with $d=1$ if $p^k=2$ and $d=\varphi(p^k)/2$ otherwise, lies in $K$.
--
--   This is the rationality step for the kernel polynomial cutting out the $\mu_{p^k}$-level structure on the Tate curve: once a variable change has been normalised so that the abscissae of the two toric $\ell_g$-torsion points become functions on $X_{H_1}(q^2M')$, the transported kernel polynomial is itself defined over that function field. It feeds the construction of rigid Weierstrass data at the Tate parameter over the level-$H_1$ function field, and thence the computation of the $j$-invariant of the resulting point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_fst_mem_range_rigidDataH1Pow.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_fst_mem_range_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))

    (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ∣ M')
    (h : Polynomial (LaurentSeries L))
    (hh : ∀ (F' : Type) [Field F'] (f : L →+* F') (ζ : F'), IsPrimitiveRoot ζ (p ^ k) →
      h.map (ModularCurve.coeffMap f) =
        ∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
          (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' q (ζ ^ a)).1))
    (C : WeierstrassCurve.VariableChange (LaurentSeries L))

    (hx₁ : ((⟨(ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1, (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2, (ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ 2)).1, (ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ 2)).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C).xP ∈ Set.range ((↑) : ↥K → LaurentSeries L))
    (hx₂ : ((⟨(ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1, (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2, (ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ 2)).1, (ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ 2)).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C).xQ ∈ Set.range ((↑) : ↥K → LaurentSeries L)) :
    ∀ i : ℕ, (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h).coeff i ∈
      Set.range ((↑) : ↥K → LaurentSeries L) := by sorry
