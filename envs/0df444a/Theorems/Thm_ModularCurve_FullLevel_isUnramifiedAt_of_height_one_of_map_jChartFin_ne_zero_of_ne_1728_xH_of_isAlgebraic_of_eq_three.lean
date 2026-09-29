-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_map_jChartFin_ne_zero_of_ne_1728_xH_of_isAlgebraic_of_eq_three
-- name    : ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_map_jChartFin_ne_zero_of_ne_1728_xH_of_isAlgebraic_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/d538f479-78e4-5556-a571-091ede2e2af3
-- title:
--   Horizontal unramifiedness over the Γ₀(M') floor, q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'\neq 0$ with $q\nmid M'$, and let $L$ be a field of characteristic zero, algebraic over $\mathbb{Q}$, containing a primitive $q$-th root of unity $\zeta$ and admitting a ring homomorphism $\iota:L\to\mathbb{C}$ with $\iota\zeta=\exp(2\pi i/q)$. Let $K$ be the intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image of the $q$-expansion function field of $X_H$ of level $q^2M'$, where $H=\mathrm{levelH}\,q\,M'$ is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$; that function field is generated over $\mathbb{Q}$ by ratios of integral $q$-expansions of modular forms of equal weight for $\Gamma_H(q^2M')$. Let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal, with $\zeta$ in the image of $A$, acting on $K$ compatibly with $L$, and let $\varpi$ generate the maximal ideal. Let $j\in K$ be nonzero with Laurent expansion the image of the $q$-expansion $\mathrm{jq}$ of the modular invariant, and let $W_0$ be the valuation subring of $K$ consisting of those $f$ for which $f\cdot y=x$ in $\mathrm{LaurentSeries}\,L$ for some power series $x,y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal. Let $z$ be a point of the two-chart integral model $\mathrm{TwoChartIntegralModel}\,A\,K\,j$ (the pushout gluing $\operatorname{Spec}$ of the algebra of elements of $K$ integral over $A[j]$ to that of the elements integral over $A[j^{-1}]$), and assume the germ at $z$ of the image of $\varpi$ under the structure morphism to $\operatorname{Spec} A$ lies in the maximal ideal of the stalk. Let $y$ be a point of $\operatorname{Spec}$ of the finite chart algebra $B=\mathrm{chartAlgFin}\,A\,K\,j$ mapping to $z$, with $\mathfrak p_y$ maximal, and let $\varphi:B\to\Omega$ be a ring homomorphism into an algebraically closed field of characteristic $q$ with kernel $\mathfrak p_y$, such that $\varphi(j)$ does not lie in $\mathrm{ssJSet}\,q\,\Omega$, the set of those $j$-values all of whose elliptic Weierstrass models have no nonzero $q$-torsion point. Assume every element of $B$ lying in $W_0^{\mathrm{nonunits}}$ lies in $\mathfrak p_y$. Let $K_0\le K$ be the analogous base change of the $\Gamma_0(M')$ $q$-expansion function field, with a nonzero $j_0\in K_0$ of the same Laurent expansion and with a ring homomorphism $\iota$ from $B_0=\mathrm{chartAlgFin}\,A\,K_0\,j_0$ to $B$ induced by the inclusion $K_0\hookrightarrow K$. Assume finally $\varphi(j)\neq 0$ and $\varphi(j)\neq 1728$. Then, with $B$ regarded as a $B_0$-algebra via $\iota$, for every prime ideal $\mathfrak Q$ of $B$ with $\mathfrak Q\le\mathfrak p_y$, of height $1$, and not containing the image of $\varpi$, the algebra $B$ is unramified over $B_0$ at $\mathfrak Q$.
--
--   This is the horizontal (characteristic-zero direction) unramifiedness of the full-level integral model over its $\Gamma_0(M')$ floor at primes lying under an ordinary closed point whose $j$-invariant avoids $0$ and $1728$, the classical statement that the covering $X_H(q^2M')\to X_0(M')$ is unramified away from the elliptic points and the cusps; the hypothesis $q=3$ replaces the condition $q\ge 5$ of the companion statement. It feeds the proof that the fibre of the two-chart integral model at such a point is a regular local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_map_jChartFin_ne_zero_of_ne_1728_xH_of_isAlgebraic_of_eq_three.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_map_jChartFin_ne_zero_of_ne_1728_xH_of_isAlgebraic_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
    (hord : φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∉ ModularCurve.ssJSet q Ω)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal)

    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle₀ : K₀ ≤ K)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ι : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hι : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), ((ι b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = IntermediateField.inclusion hle₀ (b : ↥K₀))

    (hj0 : φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ≠ 0) (hj1728 : φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ≠ 1728) :
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := ι.toAlgebra
    ∀ (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) [𝔔.IsPrime], 𝔔 ≤ y.asIdeal → 𝔔.height = 1 →
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∉ 𝔔 → Algebra.IsUnramifiedAt ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) 𝔔 := by sorry
