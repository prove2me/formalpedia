-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_map_jChartFin_mem_ssJSet_of_comap_gauss_ne_gauss_of_forall_mem_nonunits_xH
-- name    : ModularCurve.FullLevel.map_jChartFin_mem_ssJSet_of_comap_gauss_ne_gauss_of_forall_mem_nonunits_xH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/0fc9d1f3-962e-50f4-8feb-29d6e900e34d
-- title:
--   Crossing Igusa branches force a supersingular j-value
-- statement:
--   Fix a prime $q\ge 5$ and a nonzero natural number $M'$ with $q\nmid M'$. Let $L$ be a field of characteristic $0$, algebraic over $\mathbb{Q}$, containing a primitive $q$-th root of unity $\zeta$ for which some ring homomorphism $\iota_0:L\to\mathbb{C}$ sends $\zeta$ to $e^{2\pi i/q}$. Let $K$ be the intermediate field of $L\subseteq L((t))$ obtained by adjoining to $L$ the coefficientwise image of the $q$-expansion function field of $\Gamma_H$ at level $q^2M'$, where $H\le(\mathbb{Z}/q^2M')^\times$ is the kernel of reduction to $(\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$. Let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal, with $\zeta$ in the image of $A$, and with $K$ an $A$-algebra compatibly with $L$; let $\varpi$ generate the maximal ideal of $A$. Let $j\in K$, nonzero, whose Laurent series is the coefficientwise image of $t^{-1}\cdot\mathrm{jNumQ}$, the $q$-expansion of the modular invariant. Let $W_0$ be a valuation subring of $K$ consisting exactly of those $f$ for which there are power series $x,y$ over $A$ with $y$ not reducing to $0$ modulo the maximal ideal and $f\cdot y=x$ in $L((t))$ (the Gauss ring of $A$-integral $q$-expansions). Consider the two-chart integral model of $K$ over $A$ attached to $j$, the pushout of the spectra of the integral closures of $A[j]$ and of $A[j^{-1}]$ in $K$ along the middle chart, and a point $z$ of it at which the germ of the image of $\varpi$ under the structure morphism to $\operatorname{Spec} A$ lies in the maximal ideal of the stalk. Let $y$ be a point of the spectrum of the finite chart algebra $A_1$ (the elements of $K$ integral over $A[j]$) mapping to $z$, with $y$ corresponding to a maximal ideal, and let $\varphi:A_1\to\Omega$ be a ring homomorphism into an algebraically closed field $\Omega$ of characteristic $q$ with kernel that maximal ideal. Let $\tau:\mathrm{SL}_2(\mathbb{Z})\to(K\simeq_L K)$ be such that for every $\gamma\in\Gamma_0(M')$ the automorphism $\tau(\gamma)$ is a level automorphism at $\gamma^{-1}$ in the sense of `IsLevelAutAt` for the data $(q,\zeta,q,q^2M',H)$: on every quotient of $q$-expansions of weight-$k$ modular forms on $\Gamma_H(q^2M')$ with integral $q$-expansions it acts, after any embedding $\iota$ of $L$ into $\mathbb{C}$ sending $\zeta$ to $e^{2\pi i/q}$, by the slash action of the matrix $\begin{pmatrix} a & b/q\\ qc & d\end{pmatrix}$ attached to $\gamma^{-1}$. Assume finally that for some $\gamma\in\Gamma_0(M')$ the pullback of $W_0$ along $\tau(\gamma)$ differs from $W_0$, and that both branches are centred at $y$: every element of $A_1$ whose image in $K$ is a non-unit of that pullback, respectively of $W_0$, lies in the maximal ideal corresponding to $y$. Then $\varphi(j)$ lies in $\mathrm{ssJSet}\,q\,\Omega$, that is, every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(j)$ has no nonzero point killed by $q$.
--
--   This is the statement that two distinct Igusa branches of the reduction of the modular curve of level $\Gamma(q)\cap\Gamma_0(M')$ can cross only above a supersingular $j$-invariant, in the normalisation where one branch is the Gauss ring of integral $q$-expansions itself and the other is its translate by a level automorphism. It feeds the construction of the cyclic inertia action on the chart algebra used when the relevant $j$-value is not supersingular.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_map_jChartFin_mem_ssJSet_of_comap_gauss_ne_gauss_of_forall_mem_nonunits_xH.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.map_jChartFin_mem_ssJSet_of_comap_gauss_ne_gauss_of_forall_mem_nonunits_xH
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))

    [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hmax : y.asIdeal.IsMaximal)
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω)
    (hφ : RingHom.ker φ = y.asIdeal)

    (τ : SL(2, ℤ) → (↥K ≃ₐ[L] ↥K))
    (hτ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') γ⁻¹ K (τ γ))

    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (hne : W₀.comap (τ γ).toAlgHom.toRingHom ≠ W₀)
    (hz₁ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ (W₀.comap (τ γ).toAlgHom.toRingHom).nonunits → b ∈ y.asIdeal)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal) :
    φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω := by sorry
