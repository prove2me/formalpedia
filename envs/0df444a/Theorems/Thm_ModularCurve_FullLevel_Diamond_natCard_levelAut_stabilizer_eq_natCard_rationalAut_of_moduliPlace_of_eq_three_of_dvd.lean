-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_natCard_levelAut_stabilizer_eq_natCard_rationalAut_of_moduliPlace_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.Diamond.natCard_levelAut_stabilizer_eq_natCard_rationalAut_of_moduliPlace_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/c15bebf5-8894-5963-990f-a24e733f9552
-- title:
--   Level-automorphism stabiliser equals rational automorphism count, q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'>0$ with $q\nmid M'$, and let $\ell_g$ be a prime with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ in which $q$ is a non-unit (`LiesOverPrime`), let $W$ be a finite set of places of `modularFunctionFieldC (ResidueField A) M'` over $\mathrm{ResidueField}\,A$ whose members are exactly the supersingular places — rational, affine geometric places whose value at `jGeomGen` lies in `ssJSet q`, the set of $j$ such that every elliptic curve with that $j$-invariant has no non-zero $q$-torsion point — and let $s\in W$. Assume the base change `modularFunctionFieldBar M'` of the full level-$M'$ modular function field to $\overline{\mathbb Q}$ is contained in `fieldBar q M'`, the field attached to $H=\ker\big((\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times\big)$, and let $R_0$ be a constant reduction of `modularFunctionFieldBar M'` relative to $A$ with values in `modularFunctionFieldC (ResidueField A) M'` whose residue map agrees with coefficientwise reduction on Laurent series with coefficients in $A$. Let $k_0\subseteq\overline{\mathbb Q}$ be an intermediate field and $\pi_0\in k_0$ an element of $A$ such that $A\cap k_0$ is a henselian discrete valuation ring with maximal ideal $(\pi_0)$ and algebraically closed residue field, with every element of $A$ congruent to an element of $k_0\cap A$ modulo the maximal ideal of $A$, and let $\xi\in k_0$ be a primitive $q$-th root of unity. Let $H_1=\ker\big((\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times\big)\cap\ker\big((\mathbb Z/q^2M')^\times\to(\mathbb Z/\ell_g)^\times\big)$, let $K_\ell$ be the base change to $k_0$ of the function field `xHFunctionField (q^2*M') H₁` inside Laurent series over $k_0$, and let $j_\ell\in K_\ell$ be non-zero with underlying Laurent series the coefficient embedding of the $q$-expansion `jq`. Let $y$ be a maximal ideal of `chartAlgFin (A ∩ k₀) Kℓ jℓ`, the algebra of elements of $K_\ell$ integral over $(A\cap k_0)[j_\ell]$, containing $\pi_0$, such that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism from that chart algebra with kernel $y$ the image of $j_\ell$ is a supersingular $j$-invariant (lies in `ssJSet q Ω`); assume further the compatibility `hover` between $y$ and $s$: whenever $g$ lies in the full level-$M'$ modular function field, is $R_0$-integral, has non-negative order at every place at which $j$ does, has $R_0$-residue in the valuation subring of $s$, and has image lying in $K_\ell$ and in the chart algebra, then $g-c\in y$ for every $c\in k_0\cap A$ whose residue in $\mathrm{ResidueField}\,A$ is the value at $s$ of the $R_0$-residue of $g$. Finally let $E$ be an elliptic Weierstrass curve over $\mathrm{ResidueField}\,A$ and $\mathrm{Cyc}$ a cyclic subgroup of its group of affine points of order $M'$, such that the valuation subring of $s$ is the preimage of that of `moduliPlace (ResidueField A) M' E Cyc` under the inclusion of `modularFunctionFieldC` into `modularFunctionFieldFullC`. Then the number of $k_0$-automorphisms $\tau$ of $K_\ell$ such that (i) there is $\gamma\in SL(2,\mathbb Z)$ lying in $\Gamma(q)\cap\Gamma_0(M')$ with `IsLevelAutAt k₀ q ξ q (q^2*M') H₁ γ⁻¹ Kℓ τ` — that is, $\tau$ carries a quotient $f/g$ of modular forms of level $\Gamma_{H_1}(q^2M')$ with integral $q$-expansions to the quotient of the slash-translates of $f$ and $g$ by the matrix `conjElemN q γ⁻¹`, under any embedding $k_0\to\mathbb C$ sending $\xi$ to $e^{2\pi i/q}$ — and (ii) $\tau$ preserves $y$, in the sense that for every $b$ in the chart algebra with $\tau b$ again in it one has $b\in y$ if and only if $\tau b\in y$, equals the number of additive endomorphisms $\iota$ of the group of affine points of $E$ that lie in [`WeierstrassCurve.rationalHomSet (ResidueField A) E E`](def/WeierstrassCurve_RationalEnd.html#L28), admit a two-sided inverse inside that set, and satisfy $\iota(\mathrm{Cyc})=\mathrm{Cyc}$.
--
--   This is the $q=3$, $\Gamma_1(\ell_g)$-guard form of the comparison between the inertia-type stabiliser of a supersingular point in the deck group of the auxiliary covering and the automorphism group of the corresponding moduli datum $(E,\mathrm{Cyc})$ over the residue field, the local input for the width of supersingular points on the model of the modular curve. It is used by [`ModularCurve.FullLevel.Diamond.rigidChart_decompositionOrder_eq_natCard_rationalAut_of_moduliPlace_of_decompositionUnique_linkedScalars_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.Diamond.rigidChart_decompositionOrder_eq_natCard_rationalAut_of_moduliPlace_of_decompositionUnique_linkedScalars_of_eq_three_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_natCard_levelAut_stabilizer_eq_natCard_rationalAut_of_moduliPlace_of_eq_three_of_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.Diamond.natCard_levelAut_stabilizer_eq_natCard_rationalAut_of_moduliPlace_of_eq_three_of_dvd
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ q)

    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ) (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (jℓ ≠ 0)]

    (y : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hy : y.IsMaximal)
    (hϖy : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) →+* Ω), RingHom.ker φ = y → φ (jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ∈ ModularCurve.ssJSet q Ω)

    (hover :
    (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
          ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
      ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ)
        (hgC : (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
      ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
        (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) -
            algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y))

    (E : WeierstrassCurve (ResidueField ↥A)) [E.IsElliptic] (Cyc : AddSubgroup E.toAffine.Point)
    (hcyc : IsAddCyclic Cyc) (hcardCyc : Nat.card Cyc = M')
    (hP : (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring =
      (moduliPlace (ResidueField ↥A) M' E Cyc).toValuationSubring.comap
        (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) M')).toRingHom) :
    Nat.card {τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ //

        (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ) ∧

        (∀ (b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hb : τ (b : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ↔ (⟨τ (b : ↥Kℓ), hb⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y)} =
    Nat.card {ι : E.toAffine.Point →+ E.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet (ResidueField ↥A) E E ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet (ResidueField ↥A) E E, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        Cyc.map ι = Cyc} := by sorry
