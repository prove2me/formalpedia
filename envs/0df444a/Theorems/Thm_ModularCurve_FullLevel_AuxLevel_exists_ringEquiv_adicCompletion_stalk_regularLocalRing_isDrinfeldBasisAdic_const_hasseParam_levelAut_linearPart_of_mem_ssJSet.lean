-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_ringEquiv_adicCompletion_stalk_regularLocalRing_isDrinfeldBasisAdic_const_hasseParam_levelAut_linearPart_of_mem_ssJSet
-- name    : ModularCurve.FullLevel.AuxLevel.exists_ringEquiv_adicCompletion_stalk_regularLocalRing_isDrinfeldBasisAdic_const_hasseParam_levelAut_linearPart_of_mem_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/93741b1b-43ac-531a-afbc-d29ca081f051
-- title:
--   Supersingular moduli chart with Drinfeld basis and level action
-- statement:
--   Fix primes $q\ge 5$ and $\ell\ge 3$ with $\ell\ne q$, and $M'\ne 0$ with $q\nmid M'$, $\ell\nmid M'$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, with $\zeta\in L$ a primitive $q$-th and $\xi\in L$ a primitive $(q\ell)$-th root of unity. Let $K$ be the intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ generated over $L$ by the image, under coefficientwise base change, of the $q$-expansion function field of $X_H$ of level $N_0=(q\ell)^2M'$, $H$ being the kernel of the reduction $(\mathbb{Z}/N_0)^\times\to(\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, with $\zeta$ in the image of $A$, acting on $K$ compatibly, and with uniformiser $\varpi$. Let $j\in K$ be the element whose Laurent series is the image of the $j$-series $\mathrm{jq}$, assumed nonzero, and let $X=\mathrm{TwoChartIntegralModel}\,A\,K\,j$ be the pushout of the two spectra of the algebras of elements of $K$ integral over $A[j]$, resp. $A[j^{-1}]$. Let $z\in X$ be a point at which the germ of the global section pulled back from $\varpi\in A$ lies in the maximal ideal of the stalk, let $y\in\operatorname{Spec}(\mathrm{chartAlgFin})$ lie over $z$, and assume $y$ is supersingular: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from the finite chart algebra with kernel the prime of $y$, the value $\varphi(j)$ lies in $\mathrm{ssJSet}\,q\,\Omega$, the set of $j$-invariants all of whose elliptic Weierstrass models over $\Omega$ have no nonzero $q$-torsion point. Then there exist: a noetherian local ring $R_0$, complete for its maximal ideal, with finite residue field of characteristic $q$; a complete discrete valuation domain $W_1$ with a ring homomorphism $\sigma:A\to W_1$ such that $\mathfrak m_{W_1}=(\sigma\varpi)$ and $(\sigma\varpi)^{q-1}=\varepsilon_1 q$ for some unit $\varepsilon_1$; a local homomorphism $\iota_1:W_1\to R_0$; a ring isomorphism $\beta$ from the $\mathfrak m$-adic completion of the stalk of $X$ at $z$ onto $R_0$; a commutative formal group $F$ over $R_0$ together with $x_0,x_1\in R_0$ forming a Drinfeld basis of level $q$ in the adic sense (the $q$-th iterate series $F.\mathrm{nthSeries}\,q$ is a unit multiple of the Drinfeld divisor of $(x_0,x_1)$) with $\mathfrak m_{R_0}=(x_0,x_1)$; elements $T,w\in R_0$ with $w$ a unit and $\operatorname{coeff}_q(F.\mathrm{nthSeries}\,q)-wT\in(q)$; witnesses that $\mathrm{jqNModC}\,L\,(q\ell)$ lies in $K$ and in the finite chart algebra; $a_0\in W_1$, an integer $k\ge 1$ and a unit $w'\in R_0$, such that: $R_0$ is a regular local ring of Krull dimension $2$; for every $a\in A$, $\beta$ sends the germ at $z$ of the constant $a$ to $\iota_1(\sigma a)$; the image under $\beta$ of the germ at $z$ of the level-$(q\ell)$ rescaled $j$-series satisfies $\beta(\cdots)-\iota_1a_0=w'T^k$; and, for every $\gamma\in\Gamma_0(M')$ and every $L$-algebra automorphism $\tau$ of $K$ which is a level automorphism at $(L,q\ell,\xi,q\ell,N_0,H)$ for $\gamma^{-1}$, preserving the finite chart algebra and congruent to the identity on it modulo the prime of $y$, there are a ring automorphism $\theta_0$ of $R_0$ and $c\in R_0$ with: $\theta_0$ intertwining $\beta$ composed with the germ map with the action of $\tau$ on the chart algebra; $\theta_0(\iota_1(\sigma a))=\iota_1(\sigma a)$ for all $a\in A$; $\theta_0\equiv\mathrm{id}$ modulo $\mathfrak m_{R_0}$; $\theta_0x_0\equiv c(\gamma_{00}x_0+\gamma_{10}x_1)$ and $\theta_0x_1\equiv c(\gamma_{01}x_0+\gamma_{11}x_1)$ modulo $\mathfrak m_{R_0}^2$; $c^{q+1}\equiv 1$ modulo $\mathfrak m_{R_0}$; $c\equiv 1$ modulo $\mathfrak m_{R_0}$ whenever $\gamma\in\Gamma(\ell)$; and $c-1\notin\mathfrak m_{R_0}$ whenever $\gamma\in\Gamma(q)$ and $\tau$ is not the identity.
--
--   This is the moduli-theoretic description of the completed local ring of the two-chart integral model at a supersingular point of the characteristic-$q$ fibre: it is regular of dimension $2$, coordinatised by a Drinfeld basis of level $q$ of a formal group, with the Hasse parameter relating the $q$-th iterate series to a regular parameter, and with the level automorphisms attached to $\Gamma_0(M')$ acting on the basis through the reduction of $\gamma$ up to a scalar $c$ whose order divides $q+1$. It is used to obtain the corresponding statement in Drinfeld-chart coordinates, from which the local analysis of the Galois action at $q$ on the relevant modular curve proceeds.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_ringEquiv_adicCompletion_stalk_regularLocalRing_isDrinfeldBasisAdic_const_hasseParam_levelAut_linearPart_of_mem_ssJSet.lean

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

theorem ModularCurve.FullLevel.AuxLevel.exists_ringEquiv_adicCompletion_stalk_regularLocalRing_isDrinfeldBasisAdic_const_hasseParam_levelAut_linearPart_of_mem_ssJSet
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
      (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
      (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
      (a₀ : W₁) (k : ℕ) (_ : 1 ≤ k) (w' : R₀) (_ : IsUnit w'),

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

      β (toC (germY (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)))) - ι₁ a₀ = w' * T ^ k ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
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
                (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal R₀) ∧

                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal R₀)) := by sorry
