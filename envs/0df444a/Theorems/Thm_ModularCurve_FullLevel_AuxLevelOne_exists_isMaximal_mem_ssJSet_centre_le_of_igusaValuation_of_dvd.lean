-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_isMaximal_mem_ssJSet_centre_le_of_igusaValuation_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.exists_isMaximal_mem_ssJSet_centre_le_of_igusaValuation_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/95010e15-d050-5b20-a058-0c402475b39d
-- title:
--   Supersingular point strictly above the centre of an Igusa valuation
-- statement:
--   Let $q$ be a prime, $M'$ a nonzero natural number with $q \nmid M'$, and $\ell$ a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic $0$, let $\zeta \in L$ be a primitive $q$-th root of unity, and assume some ring homomorphism $L \to \mathbb{C}$ carries $\zeta$ to $e^{2\pi i/q}$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb{Z}/q)^\times$ with the kernel of reduction to $(\mathbb{Z}/\ell)^\times$, and let $K$ be the intermediate field of $L((T))/L$ generated over $L$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$ over $\mathbb{Q}$. Let $A$ be a henselian discrete valuation ring with fraction field $L$, algebraically closed residue field, uniformiser $\varpi$, with $q \in \mathfrak{m}_A$ and $\zeta$ in the image of $A$, and let $K$ be an $A$-algebra compatibly with $A \to L \to K$. Let $j \in K$ be nonzero with Laurent expansion the image of the $q$-expansion `jq` of the modular invariant, and write $C =$ `chartAlgFin A K j` for the subalgebra of elements of $K$ integral over $A[j]$, with `jChartFin A K j` denoting $j$ regarded in $C$. Let $V$ be a valuation subring of $K$ such that an element of $L$ lies in $V$ exactly when it comes from $A$, the image of $\varpi$ lies in the maximal ideal of $V$, $C \subseteq V$, and $V$ is residually transcendental over $A$ on $C$: some $c \in C$ satisfies that $p(c)$ is a unit of $V$ for every monic $p \in A[T]$. Then there is a maximal ideal $y'$ of $C$ containing the image of $\varpi$ such that (i) for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel $y'$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), i.e. every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(j)$ has no nonzero point annihilated by $q$; (ii) every $b \in C$ whose image lies in the maximal ideal of $V$ lies in $y'$; and (iii) some $b \in y'$ has image a unit of $V$, so that the centre of $V$ on $C$ is strictly contained in $y'$.
--
--   This is the Igusa-type localisation step at residue characteristic $q$ for the chart algebra of the two-chart integral model of the function field of $X_{H_1}(q^2M')$: a valuation that is residually transcendental on the $j$-finite chart has its centre strictly inside a supersingular closed point of that chart. It serves the subsequent analysis of Igusa-type valuations on the blown-up chart and of the effect of level automorphisms, in the auxiliary level construction used for small $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_exists_isMaximal_mem_ssJSet_centre_le_of_igusaValuation_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.exists_isMaximal_mem_ssJSet_centre_le_of_igusaValuation_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (V : ValuationSubring ↥K)
    (hVA : ∀ x : L, algebraMap L ↥K x ∈ V ↔ ∃ a : A, algebraMap A L a = x)
    (hϖV : ∃ hϖV : algebraMap A ↥K ϖ ∈ V, (⟨algebraMap A ↥K ϖ, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V)
    (hCV : ∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ V)
    (htr : ∃ c : ↥(chartAlgFin A (↥K) j), ∀ p : Polynomial A, p.Monic →
      ∃ hp : Polynomial.aeval ((c : ↥K)) (p.map (algebraMap A ↥K)) ∈ V, (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) :
    ∃ y' : Ideal ↥(chartAlgFin A (↥K) j), y'.IsMaximal ∧ algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y' ∧
      (∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y' → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω) ∧

      (∀ b : ↥(chartAlgFin A (↥K) j), (⟨(b : ↥K), hCV b⟩ : ↥V) ∈ maximalIdeal ↥V → b ∈ y') ∧

      (∃ b : ↥(chartAlgFin A (↥K) j), b ∈ y' ∧ (⟨(b : ↥K), hCV b⟩ : ↥V) ∉ maximalIdeal ↥V) := by sorry
