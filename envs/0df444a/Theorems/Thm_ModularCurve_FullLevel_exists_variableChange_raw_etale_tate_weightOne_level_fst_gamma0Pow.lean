-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_variableChange_raw_etale_tate_weightOne_level_fst_gamma0Pow
-- name    : ModularCurve.FullLevel.exists_variableChange_raw_etale_tate_weightOne_level_fst_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/03f39a71-f61f-5aad-b76a-c067779b24a7
-- title:
--   Raw Γ₀(M')×Γ(ℓ) structure on the twisted Tate curve
-- statement:
--   Fix a non-zero natural number $M'$ and a prime $\ell\ge 3$ with $\ell\nmid M'$, a field $L$ of characteristic zero, a primitive $\ell$-th root of unity $\zeta\in L$ admitting a ring homomorphism $\iota\colon L\to\mathbb C$ with $\iota\zeta=\exp(2\pi i/\ell)$, and the intermediate field $K$ of $L\subset L(\!(q)\!)$ obtained as `laurentBaseChange`, i.e. generated over $L$ by the coefficientwise image of the $q$-expansion function field of level $\Gamma_H(\ell^2M')$, where $H$ is the kernel of the reduction $(\mathbb Z/\ell^2M')^\times\to(\mathbb Z/\ell)^\times$, that is the units congruent to $1$ modulo $\ell$; let $A$ be a commutative ring with compatible algebra structures on $L$ and $K$. Two hypotheses are assumed, namely that for all $A$-algebras $T$ the predicate [`ModularCurve.IsLevelPStructure _ ℓ`](def/ModularCurve_KatzLevelP.html#L104) is preserved by `LevelPData.variableChange`, and that [`ModularCurve.IsGamma0PowAt _ p k`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) is preserved by [`ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k)`](def/ModularCurve_WeierstrassLevelComponents.html#L104); these are exactly the data entering `levelPComponent` and `gamma0PowComponent`. The conclusion asserts the existence of a variable change $C=(u,r,s,t)$ over $L(\!(q)\!)$ and of a raw point $x$ over $K$ for the rigidified level datum `(gamma0PowComponent A M' hM).prod ((levelPComponent A ℓ hℓ).prod (LevelComponent.trivial))` — thus a Weierstrass curve over $K$ with unit discriminant, a family $(h_p)_{p\mid M'}$ of polynomials over $K$ with $h_p$ satisfying `IsGamma0PowAt` for $p$ and $k_p=v_p(M')$, a `LevelPData` over $K$ satisfying `IsLevelPStructure` for $\ell$, and a trivial third slot — subject to four conditions. Writing $(x_0,y_0)=$ [`ModularCurve.cuspPoint L ℓ ζ ![1,0]`](def/ModularCurve_KatzLevelPCusps.html#L59), which is the Tate toric point at $\zeta$: first, $u\,(2x_0+\tfrac16)=2y_0+x_0$ and $r=-\tfrac1{12}$, $s=-\tfrac12$, $t=\tfrac1{24}$ as constant Laurent series; second, the curve of $x$, base-changed along $K\hookrightarrow L(\!(q)\!)$, equals $C\cdot$ [`ModularCurve.tateBase L ℓ`](def/ModularCurve_TateSlots.html#L46); third, for every prime $p\mid M'$, every field $F'$ with a ring homomorphism $f\colon L\to F'$ and every primitive $p^{k_p}$-th root of unity $\zeta'\in F'$, the polynomial $h_p$ pushed to $L(\!(q)\!)[X]$ and then mapped coefficientwise by $f$ equals $\mathrm{kernelVariableChangeDeg}$ of the $f$-image of $C$ in degree `gamma0PowDeg p k_p` applied to $\prod_{1\le a\le p^{k_p}/2,\ p\nmid a}\bigl(X-(\mathrm{toricPoint}\,F'\,\ell\,(\zeta'^a))_1\bigr)$; fourth, the level-$\ell$ datum of $x$, pushed to $L(\!(q)\!)$, equals the variable change by $C$ of [`ModularCurve.cuspData L ℓ ζ ![1,0] ![0,-1]`](def/ModularCurve_KatzLevelPCusps.html#L71).
--
--   This is the cusp-adapted input for the Tate curve at the cusp of $X_H(\ell^2M')$: it exhibits a point of the moduli problem combining $\Gamma_0(p^{k})$-type generator kernels at the primes dividing $M'$ with a Katz level-$\ell$ structure, realised over the function field $K$ while its curve becomes, after base change to $L(\!(q)\!)$, the weight-one-normalised Tate curve $q\mapsto q^{\ell}$. It is used by [`ModularCurve.FullLevel.exists_raw_etale_map_eq_map_qExpand_of_tatePoint`](thm.html#ModularCurve.FullLevel.exists_raw_etale_map_eq_map_qExpand_of_tatePoint).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_variableChange_raw_etale_tate_weightOne_level_fst_gamma0Pow.lean

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
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_variableChange_raw_etale_tate_weightOne_level_fst_gamma0Pow
    (M' : ℕ) [NeZero M']
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ ℓ)
    (hιζ : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (ℓ ^ 2 * M')
        (ModularCurve.FullLevel.levelH ℓ M')))
    (A : Type) [CommRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h)) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    ∃ (C : WeierstrassCurve.VariableChange (LaurentSeries L))
      (x : (((ModularCurve.gamma0PowComponent A M' hM).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid).Raw ↥K),

      (((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L ℓ (hζ.isUnit (Fact.out : ℓ.Prime).ne_zero).unit ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L ℓ (hζ.isUnit (Fact.out : ℓ.Prime).ne_zero).unit ![1, 0]).2 + (ModularCurve.cuspPoint L ℓ (hζ.isUnit (Fact.out : ℓ.Prime).ne_zero).unit ![1, 0]).1 ∧
        C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      x.curve.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L ℓ ∧

      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ' : F'),
        IsPrimitiveRoot ζ' ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((x.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' ℓ (ζ' ^ a)).1))) ∧

      x.level.2.1.map (algebraMap ↥K (LaurentSeries L)) = (ModularCurve.cuspData L ℓ (hζ.isUnit (Fact.out : ℓ.Prime).ne_zero).unit ![(1 : ZMod ℓ), 0] ![0, -(1 : ZMod ℓ)]).variableChange C := by sorry
