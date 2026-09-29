-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_det_eq_of_ker_classify_act_eq_of_relabel_gamma0Pow
-- name    : ModularCurve.FullLevel.det_eq_of_ker_classify_act_eq_of_relabel_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/d45121ef-64cf-5e5e-99c7-81a4c86a9ed3
-- title:
--   Weil pairings separate relabelled full-level components
-- statement:
--   Fix primes $q\ge 5$ and $\ell\ge 3$ with $\ell\neq q$, and a nonzero $M'$ with $q\nmid M'$, $\ell\nmid M'$. Let $L$ be a field of characteristic zero carrying a primitive $(q\ell)$-th root of unity $\xi$ and a ring homomorphism $\iota\colon L\to\mathbb C$ with $\iota\xi=\exp(2\pi i/(q\ell))$, and let $K\subseteq L(\!(T)\!)$ be the subfield generated over $L$ by the coefficientwise image of the $q$-expansion function field of $X_H$ of level $(q\ell)^2M'$, where $H$ is the kernel of $(\mathbb Z/(q\ell)^2M')^\times\to(\mathbb Z/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal and $\ell$, $M'$ units in $A$, and with $K$ an $A$-algebra through $L$; let $j\in K$ be nonzero with image the coefficientwise image of the $j$-series $q^{-1}+\dots$. Assume: level-$\ell$ Katz data (two affine points with $\mathrm{pre}\Psi_\ell$ vanishing at their abscissae and both independence elements units) and $\Gamma_0(p^k)$ kernel data are carried along variable changes; $\mathcal G$ is a family of group laws on projective Weierstrass models, chord-tangent with the origin as identity; $\mathcal T$ is a level transport at $q$ compatible with variable changes and coefficient maps; variable changes and coefficient homomorphisms are realised by graded ring maps of the projective models (hypotheses `hVC`, `hCO`). Let $P_0$ be an abstract level moduli package, of finite type over $A$, for the rigid datum $\mathrm{rigidDataPow}$ assembled from the $\Gamma_0(M')$-power, level-$\ell$ and Drinfeld-$q$ components, and let $x$ be a $K$-point of that datum whose $j$-invariant is the $(q\ell)$-fold $q$-expansion $\mathrm{jqNModC}$. Let $g_1,g_2$ be integral $2\times2$ matrices with determinant a unit modulo $q\ell$, and let $\sigma_1,\sigma_2$ be automorphisms of the moduli problem which, on raw points over any field that is an $A$-algebra, are relabelling by $g_1$ resp. $g_2$: they send the class of $y$ to the class of any $y'$ with the same curve and the same $\Gamma_0$-power datum whose level-$\ell$ datum and Drinfeld pair are the $g_i$-relabellings of those of $y$. If the classifying $A$-algebra maps $P_0.B_0\to K$ of $\sigma_1 x$ and $\sigma_2 x$ have the same kernel, then $\det g_1\equiv\det g_2$ in $\mathbb Z/\ell$ and in $\mathbb Z/q$.
--
--   This is the separation statement that the universal Weil pairings in level $\ell$ and level $q$ distinguish relabellings of a full-level structure: two relabelled points of the generic fibre landing in the same generic component must have relabelling matrices of equal determinant modulo $\ell$ and modulo $q$. It is used in the count of minimal primes for the $\Gamma_0(M')$-power full-level problem and in the comparison of classifying kernels under dense specialisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_det_eq_of_ker_classify_act_eq_of_relabel_gamma0Pow.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.det_eq_of_ker_classify_act_eq_of_relabel_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A P₀.B₀]
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L (q * ℓ))
    (g₁ g₂ : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet₁ : IsUnit (g₁.map (Int.castRingHom (ZMod (q * ℓ)))).det) (hdet₂ : IsUnit (g₂.map (Int.castRingHom (ZMod (q * ℓ)))).det)
    (σ₁ σ₂ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut)
    (hσ₁ : ∀ (T : Type) [Field T] [Algebra A T]
        (y y' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit y.level.2.2.curve.Δ),
        y'.curve = y.curve →
        y'.level.1 = y.level.1 →
        y'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel y.curve g₁ y.level.2.1 →
        y'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g₁ y.level.2.2 hΔ →
        σ₁.act (Quot.mk _ y) = Quot.mk _ y')
    (hσ₂ : ∀ (T : Type) [Field T] [Algebra A T]
        (y y' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit y.level.2.2.curve.Δ),
        y'.curve = y.curve →
        y'.level.1 = y.level.1 →
        y'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel y.curve g₂ y.level.2.1 →
        y'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g₂ y.level.2.2 hΔ →
        σ₂.act (Quot.mk _ y) = Quot.mk _ y')
    (h : RingHom.ker (P₀.classify (σ₁.act x)).toRingHom = RingHom.ker (P₀.classify (σ₂.act x)).toRingHom) :
    ((g₁.det : ℤ) : ZMod ℓ) = ((g₂.det : ℤ) : ZMod ℓ) ∧ ((g₁.det : ℤ) : ZMod q) = ((g₂.det : ℤ) : ZMod q) := by sorry
