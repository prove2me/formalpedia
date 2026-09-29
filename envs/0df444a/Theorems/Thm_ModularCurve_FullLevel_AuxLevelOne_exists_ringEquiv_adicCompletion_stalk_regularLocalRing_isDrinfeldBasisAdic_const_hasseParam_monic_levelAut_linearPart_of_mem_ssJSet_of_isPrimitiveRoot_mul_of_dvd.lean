-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_ringEquiv_adicCompletion_stalk_regularLocalRing_isDrinfeldBasisAdic_const_hasseParam_monic_levelAut_linearPart_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.exists_ringEquiv_adicCompletion_stalk_regularLocalRing_isDrinfeldBasisAdic_const_hasseParam_monic_levelAut_linearPart_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/9ca54ca9-4fd5-52ae-b2c2-a06111b49723
-- title:
--   Drinfeld chart at a supersingular point with level action
-- statement:
--   Let $q$ be a prime, $M'$ a non-zero natural number with $q \nmid M'$, and $\ell$ a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, with $\zeta \in L$ a primitive $q$-th root of unity, $\xi \in L$ a primitive $q\ell$-th root of unity and $\zeta = \xi^{\ell}$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the subgroup of units congruent to $1$ modulo $q$ and congruent to $1$ modulo $\ell$, i.e. the intersection of the kernels of the two reduction maps $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$ and $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell)^\times$, and let $K \subseteq L((T))$ be the intermediate field generated over $L$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $q$ lies in $\mathfrak m_A$ and $\zeta$ lies in the image of $A$, with uniformiser $\varpi$, $\mathfrak m_A = (\varpi)$, and with $K$ an $A$-algebra compatibly; let $j \in K$ be the element whose Laurent series is the image of the rational $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant, assumed non-zero. Let $X$ be the two-chart integral model over $A$ attached to $K$ and $j$, the pushout gluing $\operatorname{Spec}$ of the algebra of elements of $K$ integral over $A[j]$ to $\operatorname{Spec}$ of the algebra of elements integral over $A[j^{-1}]$. Let $z \in X$ be a point at which the germ of the global section coming from $\varpi$ under $X \to \operatorname{Spec} A$ lies in the maximal ideal of the stalk (so $z$ lies over the closed point of $\operatorname{Spec} A$), and let $y$ be a point of the finite-$j$ chart $\operatorname{Spec}$ of `chartAlgFin` mapping to $z$. Assume $y$ is supersingular in the sense that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from the finite-$j$ chart algebra to $\Omega$ with kernel the prime $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), i.e. every elliptic curve over $\Omega$ with that $j$-invariant has no non-zero affine point killed by $q$. Then there exist: a noetherian local ring $R_0$, complete for its maximal-ideal adic topology, with finite residue field of characteristic $q$; a complete discrete valuation domain $W_1$ with a ring homomorphism $\sigma : A \to W_1$ such that $\mathfrak m_{W_1} = (\sigma\varpi)$ and $(\sigma\varpi)^{q-1} = \varepsilon_1 q$ for a unit $\varepsilon_1$; a local homomorphism $\iota_1 : W_1 \to R_0$; a ring isomorphism $\beta$ from the $\mathfrak m$-adic completion of the stalk $\mathcal{O}_{X,z}$ onto $R_0$; a commutative formal group $F$ over $R_0$ and elements $x_0, x_1$ forming a Drinfeld basis of level $q$ in the adic sense (the $q$-th iterate series `F.nthSeries q` is a unit multiple of the Drinfeld divisor series in $x_0, x_1$) with $\mathfrak m_{R_0} = (x_0, x_1)$; elements $T$ and a unit $w$ with $\operatorname{coeff}_q(F.\mathrm{nthSeries}\, q) - wT \in (q)$; the facts that the expanded series [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18) lies in $K$ and in the finite-$j$ chart algebra; $a_0 \in W_1$, an integer $k \ge 1$, a unit $w' \in R_0$, and a monic $P \in W_1[X]$ of degree $k$ whose $i$-th coefficient for $i < k$ lies in $\mathfrak m_{W_1}^{\lfloor (k-i)q(q-1)/(q+1)\rfloor + 1}$, such that, writing $\gamma_{\mathrm{germ}}$ for the canonical map from the finite-$j$ chart algebra to $\mathcal{O}_{X,z}$ through $y$ and composing with the completion map: $R_0$ is a regular local ring of Krull dimension $2$; $\beta$ carries the image of each $a \in A$ under $A \to \mathcal{O}_{X,z} \to \widehat{\mathcal{O}}_{X,z}$ to $\iota_1(\sigma a)$; the image of [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18) satisfies $\beta(\cdot) - \iota_1 a_0 = w' \cdot (P^{\iota_1})(T)$; and, for every $\gamma \in \Gamma_0(M')$, every $L$-automorphism $\tau$ of $K$ satisfying the level-automorphism condition `IsLevelAutAt L q ζ q (q^2*M') H₁ γ⁻¹ K τ` (a $q$-expansion identity comparing $\tau$ with the action of the matrix $\mathrm{conjElemN}\,q\,\gamma^{-1}$ on quotients of modular forms of level $\Gamma_{H_1}(q^2M')$), each proof that $\tau$ preserves the finite-$j$ chart algebra, and under the assumption that the restricted $\tau$ is the identity modulo the prime $y$, there are a ring automorphism $\theta_0$ of $R_0$ and $c \in R_0$ with: $\theta_0$ conjugating $\beta$ and the germ map into the action of $\tau$ on the chart algebra; $\theta_0$ fixing every $\iota_1(\sigma a)$, $a \in A$; $\theta_0 r \equiv r \pmod{\mathfrak m_{R_0}}$ for all $r$; $\theta_0 x_0 \equiv c(\gamma_{00} x_0 + \gamma_{10} x_1)$ and $\theta_0 x_1 \equiv c(\gamma_{01} x_0 + \gamma_{11} x_1)$ modulo $\mathfrak m_{R_0}^2$; $c^{q+1} \equiv 1 \pmod{\mathfrak m_{R_0}}$; $c \equiv 1 \pmod{\mathfrak m_{R_0}}$ whenever $\gamma_{11} \equiv 1 \pmod \ell$; and $c - 1 \notin \mathfrak m_{R_0}$ whenever $\gamma \in \Gamma(q)$ and $\tau$ is not the identity on $K$.
--
--   This is the local moduli description of the two-chart integral model at a supersingular point of its characteristic-$q$ fibre: the completed local ring is regular of dimension $2$ with a Drinfeld basis of level $q$ for an attached commutative formal group, the expanded $j$-series is expressed through a monic polynomial with prescribed coefficient valuations in a Hasse parameter, and the automorphisms coming from $\Gamma_0(M')$ act on the basis through the matrix entries of $\gamma$ up to a scalar $c$ with $c^{q+1} \equiv 1$. It is the form of the chart statement used by the downstream Drinfeld-chart result, the $\ell$-diamond clause on $c$ and the $\Gamma(q)$ non-triviality clause being what separates the automorphism action from the identity for small $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_exists_ringEquiv_adicCompletion_stalk_regularLocalRing_isDrinfeldBasisAdic_const_hasseParam_monic_levelAut_linearPart_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

attribute [local instance 10000] SubalgebraClass.toAlgebra Algebra.toSMul Algebra.toModule
attribute [local instance 10001] AdicCompletion.instAlgebra

theorem ModularCurve.FullLevel.AuxLevelOne.exists_ringEquiv_adicCompletion_stalk_regularLocalRing_isDrinfeldBasisAdic_const_hasseParam_monic_levelAut_linearPart_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd
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
    ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsLocalRing R₀) (_ : IsNoetherianRing R₀)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀)
      (_ : Finite (IsLocalRing.ResidueField R₀)) (_ : CharP (IsLocalRing.ResidueField R₀) q)

      (W₁ : Type) (_ : CommRing W₁) (_ : IsDomain W₁) (_ : IsDiscreteValuationRing W₁)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁) (σ : A →+* W₁)
      (_ : IsLocalRing.maximalIdeal W₁ = Ideal.span {σ ϖ})
      (ε₁ : W₁) (_ : IsUnit ε₁) (_ : (σ ϖ) ^ (q - 1) = ε₁ * (q : W₁))
      (ι₁ : W₁ →+* R₀) (_ : IsLocalHom ι₁)

      (β : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+* R₀)

      (F : FormalGroup R₀) (_ : F.IsComm) (x₀ x₁ : R₀)
      (_ : F.IsDrinfeldBasisAdic (IsLocalRing.maximalIdeal R₀) q x₀ x₁)
      (_ : IsLocalRing.maximalIdeal R₀ = Ideal.span {x₀, x₁})

      (T : R₀) (w : R₀) (_ : IsUnit w)
      (_ : PowerSeries.coeff q (F.nthSeries q) - w * T ∈ Ideal.span {(q : R₀)})
      (hjK : ModularCurve.jqNModC L q ∈ K)
      (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
      (a₀ : W₁) (k : ℕ) (_ : 1 ≤ k) (w' : R₀) (_ : IsUnit w')

      (P : Polynomial W₁) (_ : P.Monic) (_ : P.natDegree = k)
      (_ : ∀ i < k, P.coeff i ∈ IsLocalRing.maximalIdeal W₁ ^ ((k - i) * (q * (q - 1)) / (q + 1) + 1)),

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      IsRegularLocalRing R₀ ∧ ringKrullDim R₀ = 2 ∧

      (∀ a : A, β (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        ι₁ (σ a)) ∧

      β (toC (germY (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)))) - ι₁ a₀ =
        w' * (P.map ι₁).eval T ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal) →
              ∃ (θ₀ : R₀ ≃+* R₀) (c : R₀),

                (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                  θ₀ (β (toC (germY a))) = β (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                (∀ a : A, θ₀ (ι₁ (σ a)) = ι₁ (σ a)) ∧

                (∀ r : R₀, θ₀ r - r ∈ IsLocalRing.maximalIdeal R₀) ∧

                (θ₀ x₀ - c * (((γ 0 0 : ℤ) : R₀) * x₀ + ((γ 1 0 : ℤ) : R₀) * x₁) ∈ (IsLocalRing.maximalIdeal R₀) ^ 2) ∧
                (θ₀ x₁ - c * (((γ 0 1 : ℤ) : R₀) * x₀ + ((γ 1 1 : ℤ) : R₀) * x₁) ∈ (IsLocalRing.maximalIdeal R₀) ^ 2) ∧
                (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal R₀) ∧
                (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal R₀) ∧

                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal R₀)) := by sorry
