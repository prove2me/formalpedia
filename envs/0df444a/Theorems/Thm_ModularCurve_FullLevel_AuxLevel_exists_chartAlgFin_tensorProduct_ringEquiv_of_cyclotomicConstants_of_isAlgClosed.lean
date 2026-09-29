-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_chartAlgFin_tensorProduct_ringEquiv_of_cyclotomicConstants_of_isAlgClosed
-- name    : ModularCurve.FullLevel.AuxLevel.exists_chartAlgFin_tensorProduct_ringEquiv_of_cyclotomicConstants_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/983f2ef0-59c7-58d1-aa8b-400bd3b0c2e8
-- title:
--   Base change of the j-chart along the cyclotomic constants
-- statement:
--   Fix primes $q\ge 5$ and $\ell\ge 3$ with $\ell\neq q$, and $M'\neq 0$ divisible by neither $q$ nor $\ell$. Let $L$ be a field of characteristic $0$ containing a primitive $q$-th root of unity $\zeta$ and a primitive $q\ell$-th root of unity $\xi$, and assume some ring homomorphism $L\to\mathbb{C}$ sends $\xi$ to $e^{2\pi i/(q\ell)}$. Let $K\subset L((\mathfrak q))$ be the intermediate field generated over $L$ by the coefficientwise image of the $q$-expansion function field of $X_H$ of level $(q\ell)^2M'$, where $H\le(\mathbb Z/(q\ell)^2M')^\times$ is the kernel of reduction to $(\mathbb Z/q\ell)^\times$. Let $A$ be a discrete valuation ring with fraction field $L$ and algebraically closed residue field, with $q$ in its maximal ideal, with $\zeta$ in the image of $A$, acting on $K$ compatibly, and with uniformiser $\varpi$; let $j\in K$ be the element whose Laurent expansion is the coefficientwise image of the $q$-expansion of $j$, and $j\neq 0$. Write $C=\mathrm{chartAlgFin}\,A\,K\,j$ for the subalgebra of elements of $K$ integral over $A[j]$. Let $y$ be a point of $\operatorname{Spec} C$ whose prime ideal is maximal and contains $\varpi$, and assume that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi\colon C\to\Omega$ with kernel $y$, the value $\varphi(j)$ lies in $\mathrm{ssJSet}\,q\,\Omega$, i.e. every elliptic curve over $\Omega$ with that $j$-invariant has no nonzero point killed by $q$. On the constant side, let $L_0$ be a cyclotomic extension of $\mathbb{Q}$ of level $q\ell$ with a primitive $q$-th root $\zeta_0$ and a primitive $q\ell$-th root $\xi_0$, let $i\colon L_0\to L$ satisfy $i\zeta_0=\zeta$, $i\xi_0=\xi$, let $A_0$ be a discrete valuation ring with fraction field $L_0$ and uniformiser $\varpi_0$, equipped with an injective local homomorphism $A_0\to A$ compatible with $i$ and such that an element of $L_0$ lies in $A_0$ exactly when its image under $i$ lies in $A$, and let $K_0\subset L_0((\mathfrak q))$, $j_0\in K_0$, $C_0=\mathrm{chartAlgFin}\,A_0\,K_0\,j_0$ be the corresponding data over $L_0$. Then there are a ring homomorphism $c_K\colon K_0\to K$ acting on Laurent series by applying $i$ to each coefficient, with $c_K(j_0)=j$; a ring homomorphism $c\colon C_0\to C$ induced by $c_K$ and compatible with the structure maps from $A_0$; and a ring isomorphism $\beta\colon A\otimes_{A_0}C_0\xrightarrow{\ \sim\ }C$ with $\beta(a\otimes b)=a\cdot c(b)$. Moreover the contraction $c^{-1}(y)$ is a maximal ideal of $C_0$ containing $\varpi_0$, and for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi\colon C_0\to\Omega$ with kernel $c^{-1}(y)$, the value $\varphi(j_0)$ again lies in $\mathrm{ssJSet}\,q\,\Omega$.
--
--   This is the assertion that forming the integral closure of $A[j]$ in the function field commutes with the flat base change $A_0\to A$ of discrete valuation rings, so that the $j$-finite chart of the two-chart integral model over $A$ is the base change of the corresponding chart over the cyclotomic ring of constants, together with the transport of a supersingular closed point to the smaller base. It is used in the computation of the completed local rings of the model at supersingular points, where the Drinfeld-level chart and the action of the level automorphisms on inertia are identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_chartAlgFin_tensorProduct_ringEquiv_of_cyclotomicConstants_of_isAlgClosed.lean

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

open scoped MatrixGroups TensorProduct

theorem ModularCurve.FullLevel.AuxLevel.exists_chartAlgFin_tensorProduct_ringEquiv_of_cyclotomicConstants_of_isAlgClosed
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hyϖ : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal)
    (hymax : y.asIdeal.IsMaximal)

    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (L₀ : Type) [Field L₀] [CharZero L₀] [IsCyclotomicExtension {q * ℓ} ℚ L₀]
    (ζ₀ : L₀) (hζ₀ : IsPrimitiveRoot ζ₀ q) (ξ₀ : L₀) (hξ₀ : IsPrimitiveRoot ξ₀ (q * ℓ))
    (i : L₀ →+* L) (hiζ : i ζ₀ = ζ) (hiξ : i ξ₀ = ξ)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [Algebra A₀ L₀] [IsFractionRing A₀ L₀]
    [Algebra A₀ A] [IsLocalHom (algebraMap A₀ A)] (hinj : Function.Injective (algebraMap A₀ A))
    (hA₀A : ∀ a : A₀, algebraMap A L (algebraMap A₀ A a) = i (algebraMap A₀ L₀ a))
    (hA₀ : ∀ x : L₀, (∃ a : A₀, algebraMap A₀ L₀ a = x) ↔ ∃ a : A, algebraMap A L a = i x)
    (ϖ₀ : A₀) (hϖ₀ : IsLocalRing.maximalIdeal A₀ = Ideal.span {ϖ₀})

    (K₀ : IntermediateField L₀ (LaurentSeries L₀))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L₀
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    [Algebra A₀ ↥K₀] [IsScalarTower A₀ L₀ ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L₀)) = ModularCurve.coeffEmb L₀ ModularCurve.jq) [Fact (j₀ ≠ 0)] :
    ∃ (cK : ↥K₀ →+* ↥K)
      (_ : ∀ x : ↥K₀, ((cK x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap i ((x : ↥K₀) : LaurentSeries L₀))
      (_ : cK j₀ = j)
      (c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
      (_ : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
        ((c a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = cK (a : ↥K₀))
      (_ : ∀ a : A₀, c (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) a) =
        algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (algebraMap A₀ A a))

      (β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) ≃+*
        ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
      (_ : ∀ (a : A) (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)),
        β (a ⊗ₜ[A₀] b) = algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a * c b),

      (Ideal.comap c y.asIdeal).IsMaximal ∧
      algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) ϖ₀ ∈ Ideal.comap c y.asIdeal ∧
      (∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* Ω),
          RingHom.ker φ = Ideal.comap c y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ (↥K₀) j₀) ∈ ModularCurve.ssJSet q Ω) := by sorry
