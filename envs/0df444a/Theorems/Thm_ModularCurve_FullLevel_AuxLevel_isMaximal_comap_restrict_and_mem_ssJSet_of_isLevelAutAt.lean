-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isMaximal_comap_restrict_and_mem_ssJSet_of_isLevelAutAt
-- name    : ModularCurve.FullLevel.AuxLevel.isMaximal_comap_restrict_and_mem_ssJSet_of_isLevelAutAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/59a865ae-3e0b-513c-805a-2c78ac4696c1
-- title:
--   Level automorphisms preserve supersingular maximal ideals of the j-chart
-- statement:
--   Let $q \ge 5$ and $\ell \ge 3$ be distinct primes and $M' \ge 1$ with $q \nmid M'$ and $\ell \nmid M'$. Let $L$ be a field of characteristic $0$ containing a primitive $(q\ell)$-th root of unity $\xi$, and suppose some ring homomorphism $\iota_0 \colon L \to \mathbb{C}$ sends $\xi$ to $\exp(2\pi i/(q\ell))$. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_H$ at level $N_0 = (q\ell)^2 M'$, where $H = \mathrm{levelH}\,(q\ell)\,M'$ is the kernel of $(\mathbb{Z}/N_0)^\times \to (\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$. Let $A$ be a henselian discrete valuation ring with fraction field $L$, algebraically closed residue field, uniformiser $\varpi$ generating $\mathfrak{m}_A$, with $q \in \mathfrak{m}_A$ and $\xi$ in the image of $A$, and let $A$ act on $K$ compatibly with $L$. Let $j \in K$, $j \neq 0$, be the element whose Laurent series is the coefficientwise image of the rational $q$-expansion $\mathrm{jq}$ of the modular invariant, and write $C = \mathrm{chartAlgFin}\,A\,K\,j$ for the algebra of elements of $K$ integral over $A[j]$, with $\mathrm{jChartFin}$ the element $j$ viewed in $C$. Assume that for every $\gamma \in \Gamma_0(M')$ every $L$-automorphism $\tau$ of $K$ satisfying $\mathrm{IsLevelAutAt}\,L\,(q\ell)\,\xi\,(q\ell)\,N_0\,H\,\gamma^{-1}\,K\,\tau$ — that is, for all weights $k$, all modular forms $f, g$ of level $\Gamma_H(N_0,H)$ with integral $q$-expansions, $g$ having nonzero expansion series, and all $x \in K$ reading as the ratio of those expansions, the complex reading of $\tau x$ under any $\iota$ with $\iota \xi = \exp(2\pi i /(q\ell))$ equals the ratio of the $q$-expansions of $f$ and $g$ translated by the matrix $\mathrm{conjElemN}\,(q\ell)\,\gamma^{-1}$ — maps $C$ into $C$. Fix such a $\gamma$ and $\tau$, and let $y' \subseteq C$ be a maximal ideal containing the image of $\varpi$ such that every ring homomorphism $\varphi$ from $C$ to an algebraically closed field $\Omega$ of characteristic $q$ with kernel $y'$ sends $\mathrm{jChartFin}$ into $\mathrm{ssJSet}\,q\,\Omega$, the set of $j$-invariants in $\Omega$ all of whose elliptic Weierstrass curves have no nontrivial $q$-torsion point. Then the preimage of $y'$ under the restriction of $\tau$ to $C$ is again maximal, contains the image of $\varpi$, and has the same property: every homomorphism from $C$ to an algebraically closed field of characteristic $q$ with that kernel sends $\mathrm{jChartFin}$ into $\mathrm{ssJSet}\,q\,\Omega$.
--
--   This is the statement that the supersingular closed points of the finite ($j$-integral) chart of the two-chart integral model of $K$ over $A$ are permuted by the level automorphisms attached to $\Gamma_0(M')$, together with the fact that such points lie over the closed point of $A$. It is used downstream in the construction of places of $K$ with prescribed supersingular reduction and in the analysis of the action of the level automorphisms on the reduction of the chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_isMaximal_comap_restrict_and_mem_ssJSet_of_isLevelAutAt.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.isMaximal_comap_restrict_and_mem_ssJSet_of_isLevelAutAt
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})

    (hpres : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
        ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
    (y' : Ideal ↥(chartAlgFin A (↥K) j)) (hy' : y'.IsMaximal) (hϖy' : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y')
    (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y' → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω) :
    (Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) (hpres γ hγ τ hτ)) y').IsMaximal ∧
    algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) (hpres γ hγ τ hτ)) y' ∧
    (∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) (hpres γ hγ τ hτ)) y' →
        φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω) := by sorry
