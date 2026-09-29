-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic
-- name    : ModularCurve.FullLevel.forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/bf41502f-0b40-54de-889a-a84a36865eb7
-- title:
--   Ordinary special points: valuation rings over O₀ lie over O₀'
-- statement:
--   Fix a prime $q\ge 5$ and $M'\neq 0$ with $q\nmid M'$, a field $L$ of characteristic zero, algebraic over $\mathbb Q$, containing a primitive $q$-th root of unity $\zeta$ for which some ring embedding $L\to\mathbb C$ sends $\zeta$ to $e^{2\pi i/q}$. Let $K$ be the intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise image of the $\mathbb Q$-function field of $X_H$ at level $q^2M'$, $H$ the kernel of $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$. Let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal, $\zeta$ in its image, acting on $K$ compatibly, $\varpi$ a generator of its maximal ideal, and $j\in K$ nonzero whose Laurent expansion is the coefficientwise image of $\mathrm{jq}$. Let $W_0$ be the valuation subring of $K$ consisting of the $f$ with $f\cdot y=x$ for power series $x,y$ over $A$ with $y$ not reducing to $0$ mod $\varpi$. On the two-chart integral model $\mathfrak X$ over $A$ (the pushout of the spectra of the integral closures of $A[j]$ and $A[j^{-1}]$ in $K$) take a point $z$ at which the germ of $\varpi$ lies in the maximal ideal of the stalk, coming from a maximal ideal $y$ of the finite chart $\mathrm{chartAlgFin}$; assume there is a ring map $\varphi$ from that chart to an algebraically closed field $\Omega$ of characteristic $q$ with kernel $y$ and with $\varphi(j)\notin \mathrm{ssJSet}\,q\,\Omega$, i.e. $\varphi(j)$ is not a value for which every elliptic curve with that $j$-invariant has trivial $q$-torsion; assume also that every chart element whose image in $K$ is a non-unit of $W_0$ lies in $y$. Let $K_0\subseteq K_0'\subseteq K$ be the subfields generated over $L$ by the coefficientwise images of the $\mathbb Q$-$q$-expansion function fields of $\Gamma_0(M')$ and $\Gamma_0(qM')$, with valuation subrings $O_0\subseteq K_0$ and $O_0'\subseteq K_0'$ described by the same power-series condition. The conclusion: for every valuation subring $B$ of $K$ with $B\cap K_0=O_0$ and such that every element of $\mathrm{chartAlgFin}$ whose image in $K$ is a non-unit of $B$ lies in $y$, one has $B\cap K_0'=O_0'$, that is, $\mathrm{algebraMap}\,x\in B\iff x\in O_0'$ for all $x\in K_0'$.
--
--   The statement is a rigidity assertion about branches of the special fibre at a closed point of the integral model of $X_H(q^2M')$ with ordinary $j$-invariant: of the two extensions to the $\Gamma_0(qM')$-floor of the Gauss valuation of the $\Gamma_0(M')$-floor, only the Gauss one can be induced by a valuation of $K$ whose centre passes through such a point, since otherwise the image of the point would lie on two branches of $X_0(qM')$ and the $j$-invariant would be supersingular. It is used in the unramifiedness statement at height-one points of this model and in the companion result forcing a supersingular $j$-value when the Gauss ring is not preserved.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic.lean

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

theorem ModularCurve.FullLevel.forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic
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
    (hord : φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∉ ModularCurve.ssJSet q Ω)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal)

    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (K₀' : IntermediateField L (LaurentSeries L))
    (hK₀' : K₀' = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M'))))
    (hle₀ : K₀ ≤ K₀') (hle' : K₀' ≤ K)
    (O₀ : ValuationSubring ↥K₀)
    (hO₀ : ∀ f : ↥K₀, f ∈ O₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (O₀' : ValuationSubring ↥K₀')
    (hO₀' : ∀ f : ↥K₀', f ∈ O₀' ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    letI : Algebra ↥K₀ ↥K := (IntermediateField.inclusion (hle₀.trans hle')).toRingHom.toAlgebra
    letI : Algebra ↥K₀' ↥K := (IntermediateField.inclusion hle').toRingHom.toAlgebra
    ∀ (B : ValuationSubring ↥K),
      (∀ x : ↥K₀, algebraMap ↥K₀ ↥K x ∈ B ↔ x ∈ O₀) →
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ B.nonunits → b ∈ y.asIdeal) →
        ∀ x : ↥K₀', algebraMap ↥K₀' ↥K x ∈ B ↔ x ∈ O₀' := by sorry
