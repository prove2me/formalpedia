-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_ringEquiv_adicCompletion_stalk_drinfeldChart_const_residueField_pow_hasse_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.exists_ringEquiv_adicCompletion_stalk_drinfeldChart_const_residueField_pow_hasse_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/26462b06-9652-55ba-b54c-ff13e1ad3574
-- title:
--   Drinfeld chart of a supersingular stalk carrying a Hasse datum
-- statement:
--   Fix primes $q$ and $\ell$ with $\ell \equiv 11 \pmod{12}$, and $M' \neq 0$ with $q \nmid M'$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, with $\xi$ a primitive $q\ell$-th root of unity, $\zeta = \xi^{\ell}$ a primitive $q$-th root of unity. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb{Z}/q)^\times$ ([`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22)) with the kernel of reduction to $(\mathbb{Z}/\ell)^\times$, and let $K$ be the intermediate field of $L \subset \mathrm{LaurentSeries}\,L$ generated over $L$ by the image under coefficientwise extension [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, with $\zeta$ in the image of $A$, with uniformiser $\varpi$, and compatibly an $A$-algebra structure on $K$. Let $j \in K$ be the element whose Laurent expansion is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81) and $j \neq 0$. Let $\mathfrak{X} =$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the pushout of the two affine charts $\operatorname{Spec}$ of the integral closures of $A[j]$ and $A[j^{-1}]$ in $K$. Let $z \in \mathfrak{X}$, let $\varpi_z$ be the image of $\varpi$ in the stalk at $z$ along the structure morphism to $\operatorname{Spec} A$, and assume $\varpi_z$ lies in the maximal ideal of that stalk. Let $y$ be a point of the $j$-finite chart $\operatorname{Spec}$ `chartAlgFin A K j` with image $z$, and assume that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from `chartAlgFin A K j` to $\Omega$ with kernel the prime of $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of $\jmath$ such that every elliptic curve over $\Omega$ with $j$-invariant $\jmath$ has no nonzero point killed by $q$. Then there exist a complete discrete valuation domain $W$, a ring homomorphism $\sigma : A \to W$ whose value $\sigma\varpi$ generates the maximal ideal of $W$, power series $f, u, v \in W[[X_0, X_1]]$ with $u, v$ units and $f - (X_0X_1^q - X_0^qX_1) \in (X_0, X_1)^{q+2}$, and a ring isomorphism $e$ from the $\mathfrak{m}$-adic completion of the stalk of $\mathfrak{X}$ at $z$ onto $S = W[[X_0, X_1]]/(C(\sigma\varpi)\,v - f\,u)$, such that: (i) for every $a \in A$, $e$ carries the image in the completion of the germ at $z$ of $a$ to the class of the constant $C(\sigma a)$; (ii) every element $x$ of the residue field of $W$ satisfies $x^{q^n} = x$ for some $n \ge 1$; and (iii) the Laurent series [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18), the image of the $j$-expansion `jqModC L` under the substitution `qExpand L q` raising the variable to the $q$-th power, lies in $K$ and indeed in `chartAlgFin A K j`, and there are $a_0 \in W$, $e_0 \ge 1$ and $h \in (X_0, X_1)^{e_0}$ with $h$ having unit leading form in the strong sense that $\sum_{i=0}^{e_0} h_{(i, e_0-i)}a^ib^{e_0-i}$ is a unit of $W$ whenever $a, b \in W$ with at least one of them a unit and $a^qb - ab^q$ in the maximal ideal, such that the image of the germ at $z$ of that element of the finite chart, transported by $e$ into $S$, differs from the class of $C(a_0)$ by the class of $h$.
--
--   This is the local structure of the completed stalk of the two-chart integral model at a supersingular point in the cyclotomic frame with a $\Gamma_1$-type condition at the guard prime $\ell \equiv 11 \pmod{12}$: the completion is a Drinfeld chart $W[[X_0,X_1]]/(\sigma\varpi\,v - f\,u)$ with $f$ congruent to the Drinfeld form $X_0X_1^q-X_0^qX_1$ modulo $(X_0,X_1)^{q+2}$, $A$-constants read through $\sigma$, and the germ of the shifted $j$-expansion differing from a constant by a power series with everywhere-unit leading form (the Hasse datum). It is the existential, one-witness form of the statement, valid for all primes $q$ (in particular $q \in \{2,3\}$), and it is cited by [`ModularCurve.FullLevel.AuxLevelOne.exists_sub_const_eq_mk_of_mem_pow_isUnit_homogeneous_drinfeldChart_of_ringEquiv_adicCompletion_stalk_of_isPrimitiveRoot_mul_of_dvd`](thm.html#ModularCurve.FullLevel.AuxLevelOne.exists_sub_const_eq_mk_of_mem_pow_isUnit_homogeneous_drinfeldChart_of_ringEquiv_adicCompletion_stalk_of_isPrimitiveRoot_mul_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_exists_ringEquiv_adicCompletion_stalk_drinfeldChart_const_residueField_pow_hasse_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevelOne.exists_ringEquiv_adicCompletion_stalk_drinfeldChart_const_residueField_pow_hasse_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hζξ : ζ = ξ ^ ℓ)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W)
      (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
      (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
      (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
        MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u}),

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) ∧

      (∀ x : IsLocalRing.ResidueField W, ∃ n : ℕ, 1 ≤ n ∧ x ^ (q ^ n) = x) ∧

    (∃ (hjK : ModularCurve.jqNModC L q ∈ K)
       (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
       (a₀ : W) (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W)
       (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e₀),
       (∀ a b : W, (a ∉ IsLocalRing.maximalIdeal W ∨ b ∉ IsLocalRing.maximalIdeal W) →
          a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W →
          IsUnit (∑ i ∈ Finset.range (e₀ + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
       (e : CMP →+* S) (toC (germY (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)))) - mkS (MvPowerSeries.C a₀) = mkS h) := by sorry
