-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_pt_laurentBaseChange_jOf_eq_jqNModC_gamma0Pow_of_algebra
-- name    : ModularCurve.FullLevel.exists_pt_laurentBaseChange_jOf_eq_jqNModC_gamma0Pow_of_algebra
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/68c926be-7532-5f1e-8c00-945798cde272
-- title:
--   Tate point of the full-level moduli datum over K
-- statement:
--   Let $q\ge 5$ and $\ell\ge 3$ be primes with $\ell\neq q$, and let $M'$ be a nonzero natural number with $q\nmid M'$ and $\ell\nmid M'$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, let $\zeta\in L$ be a primitive $q$-th root of unity and $\xi\in L$ a primitive $q\ell$-th root of unity. Let $K$ be the intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise images under $\mathbb{Q}\to L$ of the $q$-expansion function field of level $\Gamma_H$ of modulus $(q\ell)^2M'$, where $H=$ [`ModularCurve.FullLevel.levelH (q * ℓ) M'`](def/ModularCurve_FullLevelJacobian.html#L22) is the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal and $\zeta$ in the image of $A\to L$, and with $K$ an $A$-algebra over $L$; let $j\in K$ be a nonzero element whose image in $\mathrm{LaurentSeries}\,L$ is the coefficientwise image of the rational $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular $j$-function. Let $A_0$ be a commutative ring acting on $K$, and assume: (i) over every $A_0$-algebra $T$, the predicate [`ModularCurve.IsLevelPStructure · ℓ ·`](def/ModularCurve_KatzLevelP.html#L104) is preserved by variable changes acting on `LevelPData` (so that a pair of $\ell$-torsion data — two points on the affine curve whose $x$-coordinates are roots of $\mathrm{pre}\Psi_\ell$ and whose mutual independence elements are units — transports along $C\bullet W$); (ii) over every $A_0$-algebra, [`ModularCurve.IsGamma0PowAt W p k h`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) (for $p^k=2$ the two-kernel condition, otherwise the cyclic generator-kernel conditions: $\deg h\le \varphi(p^k)/2$, leading coefficient $1$ at $\varphi(p^k)/2$, $h\cdot\mathrm{pre}\Psi_{p^{k-1}}\mid \mathrm{pre}\Psi_{p^k}$, and stability of $h$ under the scalar numerators for $2\le a\le (p^k-1)/2$, $p\nmid a$) is preserved under `kernelVariableChangeDeg`; (iii) a family $\mathcal{G}$ of relative group laws on the projective models of discriminant-unit Weierstrass curves over $A_0$-algebras which is chord–tangent (compatible with point evaluation over fields and with Galois twisting) and whose identity section lies in the origin chart with $x/y=z/y=0$; (iv) a level transport $\mathcal{T}$ for $\mathcal{G}$ at $q$ satisfying the section-transport compatibilities; and (v) for all $A_0$-algebras, the existence of graded ring homomorphisms between the graded coordinate rings of projective models realising variable changes, respectively coefficient maps along $A_0$-algebra homomorphisms, and dominating the irrelevant ideal. Then the level moduli datum attached to `rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯` — whose points over a ring are variable-change classes of a Weierstrass curve with unit discriminant equipped with generator-kernel polynomials for each prime power $p^{v_p(M')}\,\|\,M'$, an $\ell$-level `LevelPData`, and a Drinfeld basis of level $q$ for $\mathcal{G}$ — has a point $x$ over $K$ whose $j$-invariant, viewed in $\mathrm{LaurentSeries}\,L$, equals [`ModularCurve.jqNModC L (q * ℓ)`](def/ModularCurve_JqCoeff.html#L18), the $q$-expansion of $j$ with the parameter raised to the power $q\ell$.
--
--   This produces the Tate (cuspidal) $K$-point of the rigidified full-level moduli problem $\Gamma_0(M')\times\Gamma(\ell)\times\Gamma(q)^{\mathrm{Dr}}$, the Tate curve over the $q$-expansion field carrying its canonical cyclic $p^{v_p(M')}$-subgroups, an $\ell$-level structure built from the cusp data, and a Drinfeld basis of its $q$-torsion. It is used in the passage from the moduli datum to the completed local ring at the cusp, in the construction of the level moduli package with $\Gamma_0$-part of general modulus $M'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_pt_laurentBaseChange_jOf_eq_jqNModC_gamma0Pow_of_algebra.lean

import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_pt_laurentBaseChange_jOf_eq_jqNModC_gamma0Pow_of_algebra
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (A₀ : Type) [CommRing A₀] [Algebra A₀ ↥K]
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ) :
    ∃ x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K,
      (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
        ModularCurve.jqNModC L (q * ℓ) := by sorry
