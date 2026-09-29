-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_coeffMap_mem_chartAlgFin_and_sub_mem_asIdeal_of_drinfeldChartWitness_anchor_of_mem_ssJSet_twoChartIntegralModel
-- name    : ModularCurve.FullLevel.AuxLevel.coeffMap_mem_chartAlgFin_and_sub_mem_asIdeal_of_drinfeldChartWitness_anchor_of_mem_ssJSet_twoChartIntegralModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/aa2833e8-85d9-5d70-bcd0-c0b93ca4e76b
-- title:
--   Inertial coefficientwise automorphisms preserve the j-chart and fix y
-- statement:
--   Fix primes $q\ge 5$ and $\ell\ge 3$ with $\ell\neq q$, and $M'\neq 0$ divisible by neither, a characteristic-zero field $L$ that is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, a primitive $q$-th root $\zeta$ and a primitive $q\ell$-th root $\xi$ in $L$, and let $K\subseteq\mathrm{LaurentSeries}\,L$ be the intermediate field obtained by adjoining to $L$ the coefficientwise image of the function field `xHFunctionField` at level $(q\ell)^2M'$ for the subgroup `levelH` $(q\ell)\,M'$, the kernel of the reduction map of unit groups. Let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal, with $\zeta$ in the image of $A$, and with $K$ an $A$-algebra compatibly; let $\varpi$ generate $\mathfrak m_A$, and let $j\in K$ be the element whose Laurent series is the coefficient image of the $q$-expansion `jq`, assumed nonzero. Let $z$ be a point of [`AlgebraicCurve.TwoChartIntegralModel`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) $A\,K\,j$ (the pushout of the two affine charts) at whose stalk the germ $\varpi z$ coming from $\varpi$ through the structure map to $\operatorname{Spec} A$ lies in the maximal ideal, and let $y$ be a point of $\operatorname{Spec}$ of the chart algebra `chartAlgFin` $A\,K\,j$ mapping to $z$ under `ιFin`. Assume $y$ is supersingular in the sense that for every algebraically closed field $\Omega$ of characteristic $q$ (with decidable equality) and every ring homomorphism $\varphi$ from the chart algebra with kernel $y.\mathrm{asIdeal}$, the value $\varphi(\,$`jChartFin`$\,)$ lies in `ssJSet` $q\,\Omega$, i.e. every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has no nonzero $q$-torsion point. Assume further a chart witness: a complete discrete valuation domain $W$, a ring map $\sigma:A\to W$ with $\mathfrak m_W=(\sigma\varpi)$, power series $f,u,v\in W[[X_0,X_1]]$ with $u,v$ units and $f-(X_0X_1^q-X_0^qX_1)\in(X_0,X_1)^{q+2}$, and a ring isomorphism $e$ from the $\mathfrak m$-adic completion of the stalk at $z$ onto $S:=W[[X_0,X_1]]/(C(\sigma\varpi)v-fu)$, together with the anchor clause: for every prime $P$ of $S$ containing the image of $C(\sigma\varpi)$ but not both images of $X_0,X_1$, and containing $X_0+h$ for some $h\in(X_0,X_1)^2$, an element $a$ of the chart algebra has its germ at $z$, viewed in the completion, in the contraction of $P$ along $e$ if and only if every Laurent coefficient of $a$ lies in $\mathfrak m_A$. The conclusion asserts: for all ring automorphisms $\sigma_L$ of $L$ and $\sigma_A$ of $A$ compatible through $A\to L$, with $\sigma_A(a)-a\in\mathfrak m_A$ for all $a$, and every ring automorphism $\tau$ of $K$ acting on Laurent series coefficientwise by $\sigma_L$, both $\tau$ and $\tau^{-1}$ map the chart algebra `chartAlgFin` $A\,K\,j$ into itself, and, for any proof that $\tau$ does so, the induced endomorphism of the chart algebra satisfies $\tau(a)-a\in y.\mathrm{asIdeal}$ for every $a$ in it.
--
--   This is the witness-independent part of the tame-inertia analysis at a supersingular point of the integral two-chart model: an automorphism of $K$ acting coefficientwise by an automorphism of $L$ that is trivial modulo $\mathfrak m_A$ preserves the $j$-finite chart algebra in both directions and acts trivially on the residue field of the supersingular point $y$. It feeds the semilinearity statement [`ModularCurve.FullLevel.AuxLevel.inertia_drinfeldChart_semilinear_linearPart_diagOneElem_of_linearPart_riders_twoChartIntegralModel`](thm.html#ModularCurve.FullLevel.AuxLevel.inertia_drinfeldChart_semilinear_linearPart_diagOneElem_of_linearPart_riders_twoChartIntegralModel), where the linear part of the inertia action on the Drinfeld chart is computed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_coeffMap_mem_chartAlgFin_and_sub_mem_asIdeal_of_drinfeldChartWitness_anchor_of_mem_ssJSet_twoChartIntegralModel.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.coeffMap_mem_chartAlgFin_and_sub_mem_asIdeal_of_drinfeldChartWitness_anchor_of_mem_ssJSet_twoChartIntegralModel
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
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
      [IsAdicComplete (IsLocalRing.maximalIdeal W) W] (σ : A →+* W)
      (hσϖ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
      (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
      (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
        MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})

    (hanchor :

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

      (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
        mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h) ∈ P) →
        ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
          toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
            ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
              (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m))
    :
      ∀ (σL : L ≃+* L) (σA : A ≃+* A),

        (∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a)) →

        (∀ a : A, σA a - a ∈ IsLocalRing.maximalIdeal A) →
        ∀ τ : ↥K ≃+* ↥K,

          (∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L)) →

          (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧
          (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
            τ.symm a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),

            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal)) := by sorry
