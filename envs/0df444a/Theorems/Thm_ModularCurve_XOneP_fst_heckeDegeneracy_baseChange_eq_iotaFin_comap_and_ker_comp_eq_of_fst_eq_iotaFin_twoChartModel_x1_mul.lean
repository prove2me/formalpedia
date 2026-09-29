-- Prove2me | Theorems.Thm_ModularCurve_XOneP_fst_heckeDegeneracy_baseChange_eq_iotaFin_comap_and_ker_comp_eq_of_fst_eq_iotaFin_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.fst_heckeDegeneracy_baseChange_eq_iotaFin_comap_and_ker_comp_eq_of_fst_eq_iotaFin_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/d987ad8f-f1bf-589d-9cc6-ea9f44126f53
-- title:
--   Hecke legs track chart primes under ι_α, ι_β
-- statement:
--   Fix a prime $p$, an integer $M \geq 5$ with $p \nmid M$, a field $L$ of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ for $\{p\}$, a primitive $p$-th root of unity $\zeta \in L$, and let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image of the function field $x1FunctionField (Mp)$; let $A$ be a discrete valuation ring with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly, and $j \in K$ nonzero mapping to the coefficientwise image of the $q$-expansion $jq$. Let $\ell$ be a prime, and let $K_\ell$ be the analogous base change of $x1x0FunctionFieldC \mathbb{Q} (Mp) (Mp\ell)$, with $j_\ell \in K_\ell$ nonzero mapping to the same $q$-expansion; assume $HeckeBetaOneDefined (Mp) \ell$, i.e. $\mathrm{qExpand}_{\mathbb{Q},\ell}$ carries $x1FunctionField (Mp)$ into $x1x0FunctionFieldC \mathbb{Q} (Mp) (Mp\ell)$. Assume given two morphisms $\pi_\alpha, \pi_\beta$ of two-chart models over $\mathrm{Spec}\,A$, from the model attached to $(K_\ell, j_\ell)$ to the one attached to $(K, j)$, both finite and surjective on points, and two $A$-algebra maps $\iota_\alpha, \iota_\beta$ between the corresponding finite chart algebras, $\iota_\alpha$ inducing the inclusion of Laurent series and $\iota_\beta$ inducing $\mathrm{qExpand}_{L,\ell}$, such that $\iota^{\mathrm{Fin}}_\ell$ followed by $\pi_\alpha$ (resp. $\pi_\beta$) equals $\mathrm{Spec}(\iota_\alpha)$ (resp. $\mathrm{Spec}(\iota_\beta)$) followed by $\iota^{\mathrm{Fin}}$. Assume further an algebraically closed field $k$ of characteristic $p$ which is an $A$-algebra, two proper smooth relative-dimension-one geometrically integral curves $C_1, C_2$ over $k$ closed-immersed into the base change to $k$ of the model of $(K,j)$ whose images together cover all points of that base change, morphisms $\pi_{\alpha,k}, \pi_{\beta,k}$ of the base-changed models compatible with both pullback projections with $\pi_\alpha$, $\pi_\beta$, and $\ell \neq p$. Then for every point $z$ of the base-changed roof and every point $y_\ell$ of $\mathrm{Spec}$ of the finite chart algebra of $(K_\ell, j_\ell)$ with $\mathrm{pr}_1(z) = \iota^{\mathrm{Fin}}_\ell(y_\ell)$: $\mathrm{pr}_1(\pi_{\alpha,k}(z)) = \iota^{\mathrm{Fin}}(\iota_\alpha^{-1} y_\ell)$, $\mathrm{pr}_1(\pi_{\beta,k}(z)) = \iota^{\mathrm{Fin}}(\iota_\beta^{-1} y_\ell)$, and for every field $\Omega$ and ring homomorphism $\varphi_\ell$ from the finite chart algebra of $(K_\ell,j_\ell)$ to $\Omega$ with kernel the prime $y_\ell$, the kernels of $\varphi_\ell \circ \iota_\alpha$ and $\varphi_\ell \circ \iota_\beta$ are the contracted primes $\iota_\alpha^{-1} y_\ell$ and $\iota_\beta^{-1} y_\ell$.
--
--   This is the dictionary translating the two Hecke degeneracy legs above $X_1(Mp)$, in the affine $j$-finite chart, into contraction of primes along the chart algebra maps $\iota_\alpha, \iota_\beta$, together with the corresponding statement for $\Omega$-valued points. It is used in the analysis of the mod $p$ special fibre of the two-chart model, where crossing points are matched with supersingular chart primes and the $\Phi_\ell$-relation between the two $j$-values along the legs is exploited.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_fst_heckeDegeneracy_baseChange_eq_iotaFin_comap_and_ker_comp_eq_of_fst_eq_iotaFin_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.fst_heckeDegeneracy_baseChange_eq_iotaFin_comap_and_ker_comp_eq_of_fst_eq_iotaFin_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (ℓ : ℕ) [Fact ℓ.Prime]

    [Algebra A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    [IsScalarTower A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    (jℓ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
    (hjℓ : ((jℓ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (jℓ ≠ 0)]

        (hβ : ModularCurve.HeckeBetaOneDefined (M * p) ℓ)

    (πα πβ : SchemeHomOver (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (ModularCurve.TwoChart.modelTo A (↥K) j))
    [IsFinite πα.1] [IsFinite πβ.1]
    (hsurjα : Function.Surjective πα.1.base) (hsurjβ : Function.Surjective πβ.1.base)
    (ια ιβ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →ₐ[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ))
    (hια : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ια b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = ((b : ↥K) : LaurentSeries L))
    (hιβ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ιβ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) =
      ModularCurve.qExpand L ℓ ((b : ↥K) : LaurentSeries L))
    (hπα : ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πα.1 = Spec.map (CommRingCat.ofHom ια.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)
    (hπβ : ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πβ.1 = Spec.map (CommRingCat.ofHom ιβ.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)

    (παk πβk : pullback (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (hπαk₁ : παk ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A k) ≫ πα.1)
    (hπαk₂ : παk ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A k))
    (hπβk₁ : πβk ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A k) ≫ πβ.1)
    (hπβk₂ : πβk ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A k))
    (hℓp : ℓ ≠ p)
    (z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A k)))
    (yℓ : ↥(ModularCurve.TwoChart.XFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ))
    (hz : (pullback.fst (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A k)).base z = (ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ).base yℓ) :
    (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (παk.base z) =
        (ModularCurve.TwoChart.ιFin A (↥K) j).base (PrimeSpectrum.comap ια.toRingHom yℓ) ∧
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (πβk.base z) =
        (ModularCurve.TwoChart.ιFin A (↥K) j).base (PrimeSpectrum.comap ιβ.toRingHom yℓ) ∧
      ∀ (Ω : Type) [Field Ω] (φℓ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) →+* Ω),
        RingHom.ker φℓ = yℓ.asIdeal →
          RingHom.ker (φℓ.comp ια.toRingHom) = (PrimeSpectrum.comap ια.toRingHom yℓ).asIdeal ∧
          RingHom.ker (φℓ.comp ιβ.toRingHom) = (PrimeSpectrum.comap ιβ.toRingHom yℓ).asIdeal := by sorry
