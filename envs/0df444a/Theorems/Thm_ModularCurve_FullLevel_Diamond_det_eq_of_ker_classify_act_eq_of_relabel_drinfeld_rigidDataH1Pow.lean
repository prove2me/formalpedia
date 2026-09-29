-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_det_eq_of_ker_classify_act_eq_of_relabel_drinfeld_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.det_eq_of_ker_classify_act_eq_of_relabel_drinfeld_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/783871ea-533b-594e-8b6c-4c185784aa41
-- title:
--   Drinfeld relabellings with equal classifying kernels have congruent determinants
-- statement:
--   Fix a prime $q$, a nonzero $M'$ with $q \nmid M'$, and a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$ and $\ell_g \mid M'$. Let $L$ be a field of characteristic zero carrying a primitive $(q\ell_g)$-th root of unity $\xi$ and a ring homomorphism $L \to \mathbb{C}$ sending $\xi$ to $\exp(2\pi i/(q\ell_g))$; let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the group of units congruent to $1$ both modulo $q$ and modulo $\ell_g$ (the intersection of the kernels of the two reduction maps), and let $K \subseteq L((\mathsf q))$ be the subfield generated over $L$ by the coefficientwise image of the function field of $X_{H_1}(q^2M')$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, with $\ell_g$ and $M'$ units, and with $K$ an $A$-algebra compatibly; let $j \in K$ be nonzero with $\mathsf q$-expansion the image of $\mathsf{jq}$. Hypotheses $h\ell$, $hM$, $hL$ assert that the $\Gamma_1(\ell_g)$-point condition (the affine equation at $(x_P,y_P)$, vanishing of $\mathrm{pre}\Psi_{\ell_g}$ at $x_P$, and $x_Q = x_P$, $y_Q = y_P$), the $\Gamma_0$-type cyclic-kernel/two-kernel condition, and divisibility of `inLineMulPoly` are preserved by variable changes; $\mathcal{G}$ is a family of relative group laws on projective Weierstrass models over $A$-algebras with invertible discriminant, assumed chord–tangent and with the origin as identity, $\mathcal{T}$ a level transport for $\mathcal{G}$ at $q$ compatible with sections, and $hVC$, $hCO$ provide graded ring maps on projective-model gradings realising variable changes and coefficient maps, with the irrelevant-ideal condition. Let $P_0$ be a fine moduli package, of finite type over $A$, for the moduli datum attached to `rigidDataH1Pow` (the restricted product of the $\Gamma_0$-component at $M'$, the $\Gamma_1(\ell_g)$-component and the Drinfeld $q$-level component, cut out by the $\Gamma_1$-link condition), and let $x$ be a $K$-point whose $j$-invariant has $\mathsf q$-expansion `jqNModC L q`. Finally let $g_1, g_2 \in M_2(\mathbb{Z})$ have determinants invertible modulo $q$, and let $\sigma_1, \sigma_2$ be automorphisms of the moduli problem which, on points over fields, send the class of a raw datum $y$ with invertible discriminant to the class of any $y'$ having the same curve, the same $\Gamma_0$- and $\Gamma_1$-components, and Drinfeld pair obtained from that of $y$ by the integral relabelling by $g_1$, respectively $g_2$ (i.e. $(P,Q) \mapsto (g_{00}P + g_{10}Q,\, g_{01}P + g_{11}Q)$ in the group law). If the kernels of the classifying $A$-algebra maps $P_0.B_0 \to K$ of $\sigma_1 x$ and of $\sigma_2 x$ coincide, then $\det g_1 \equiv \det g_2 \pmod q$.
--
--   This is the Weil-pairing separation step for the $H_1$-level moduli problem: the $q$-adic Drinfeld pairing of the relabelled Tate datum changes by $\det g$, so relabellings with non-congruent determinants carry the Tate point to points with distinct classifying kernels, i.e. to distinct components. It feeds the counts of minimal primes and the surjectivity-type statements for the $H_1$-level Jacobian, being cited by [`ModularCurve.FullLevel.Diamond.finite_minimalPrimes_and_ncard_eq_sub_one_of_jOf_eq_jqNModC_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.finite_minimalPrimes_and_ncard_eq_sub_one_of_jOf_eq_jqNModC_rigidDataH1Pow) and [`ModularCurve.FullLevel.Diamond.forall_exists_algEquiv_comap_ker_classify_eq_of_dense_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.forall_exists_algEquiv_comap_ker_classify_eq_of_dense_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_det_eq_of_ker_classify_act_eq_of_relabel_drinfeld_rigidDataH1Pow.lean

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
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.det_eq_of_ker_classify_act_eq_of_relabel_drinfeld_rigidDataH1Pow
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
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓg : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
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
    (P₀ : LevelModuliPackageAbs A (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A P₀.B₀]
    (x : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L q)
    (g₁ g₂ : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet₁ : IsUnit (g₁.map (Int.castRingHom (ZMod q))).det) (hdet₂ : IsUnit (g₂.map (Int.castRingHom (ZMod q))).det)
    (σ₁ σ₂ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.ProblemAut)
    (hσ₁ : ∀ (T : Type) [Field T] [Algebra A T]
        (y y' : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T) (hΔ : IsUnit y.level.2.2.curve.Δ),
        y'.curve = y.curve →
        y'.level.1 = y.level.1 →
        y'.level.2.1 = y.level.2.1 →
        y'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g₁ y.level.2.2 hΔ →
        σ₁.act (Quot.mk _ y) = Quot.mk _ y')
    (hσ₂ : ∀ (T : Type) [Field T] [Algebra A T]
        (y y' : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T) (hΔ : IsUnit y.level.2.2.curve.Δ),
        y'.curve = y.curve →
        y'.level.1 = y.level.1 →
        y'.level.2.1 = y.level.2.1 →
        y'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g₂ y.level.2.2 hΔ →
        σ₂.act (Quot.mk _ y) = Quot.mk _ y')
    (h : RingHom.ker (P₀.classify (σ₁.act x)).toRingHom = RingHom.ker (P₀.classify (σ₂.act x)).toRingHom) :
    ((g₁.det : ℤ) : ZMod q) = ((g₂.det : ℤ) : ZMod q) := by sorry
