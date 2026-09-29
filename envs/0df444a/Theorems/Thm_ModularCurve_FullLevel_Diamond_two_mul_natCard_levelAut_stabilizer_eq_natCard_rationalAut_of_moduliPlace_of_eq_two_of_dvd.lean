-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_two_mul_natCard_levelAut_stabilizer_eq_natCard_rationalAut_of_moduliPlace_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.Diamond.two_mul_natCard_levelAut_stabilizer_eq_natCard_rationalAut_of_moduliPlace_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/b5d2407b-dca4-587d-b803-ff3b57392227
-- title:
--   Stabiliser of a supersingular point versus Aut(E,C) at q=2
-- statement:
--   Fix a prime $q$ with $q=2$, a nonzero $M'$ with $q \nmid M'$, and a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$ and $\ell_g \mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A)\,M'$ over $\mathrm{ResidueField}\,A$ whose members are exactly the places in `ssPlaces q M' (ResidueField A)` (rational places satisfying `IsAffineGeomPlace` at which the value of `jGeomGen` lies in `ssJSet q`, i.e. is supersingular), and let $s \in W$. Assume $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a `ConstantReduction` of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with residue field $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A)\,M'$, whose residue map is compatible with coefficientwise reduction of Laurent series over $A$ (hypothesis $hR_0$). Let $k_0 \subseteq \overline{\mathbb Q}$ be an intermediate field and $\pi_0 \in k_0$ an element of $A$ such that $A \cap k_0$ is a Henselian discrete valuation ring with maximal ideal $(\pi_0)$ and algebraically closed residue field, and such that every element of $A$ is congruent modulo the maximal ideal of $A$ to an element of $k_0 \cap A$; let $\xi \in k_0$ be a primitive $q$th root of unity. Let $H_1 \le (\mathbb Z/q^2M')^\times$ be the intersection of `levelH q M'` (the units congruent to $1$ modulo $q$, i.e. the kernel of reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$) with the kernel of reduction to $(\mathbb Z/\ell_g)^\times$, and let $K_\ell$ be the base change to $k_0$ of the $q$-expansion function field $\mathrm{xHFunctionField}\,(q^2M')\,H_1$, equipped with an $A \cap k_0$-algebra structure compatible with $k_0$, together with $j_\ell \in K_\ell$ nonzero whose Laurent series is the coefficientwise image of $j_q$. Let $y$ be a maximal ideal of the chart algebra $\mathrm{chartAlgFin}\,(A\cap k_0)\,K_\ell\,j_\ell$ (the elements of $K_\ell$ integral over $(A\cap k_0)[j_\ell]$) containing the image of $\pi_0$, such that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism from the chart algebra to $\Omega$ with kernel $y$ the image of $j_\ell$ lies in `ssJSet q Ω`; assume further the compatibility $hover$, which says that for every $g$ in the full modular function field of level $M'$ over $\mathbb Q$ whose base change lies in $R_0$.integers, is regular at every place of $\mathrm{modularFunctionFieldBar}\,M'$ where $j$ is, has $R_0$-residue in the valuation subring of $s$, and lies in $K_\ell$ and in the chart algebra, and for every $c \in k_0 \cap A$ whose residue in $\mathrm{ResidueField}\,A$ is the value at $s$ of that residue, the difference $g - c$ lies in $y$. Finally let $E$ be an elliptic Weierstrass curve over $\mathrm{ResidueField}\,A$ and $\mathrm{Cyc}$ a cyclic subgroup of its affine points of order $M'$, and assume the valuation subring of $s$ is the preimage, under the inclusion of $\mathrm{modularFunctionFieldC}$ into $\mathrm{modularFunctionFieldFullC}$, of the valuation subring of $\mathrm{moduliPlace}(\mathrm{ResidueField}\,A)\,M'\,E\,\mathrm{Cyc}$. The conclusion is the numerical identity $2 \cdot n = m$, where $n$ is the number of $k_0$-algebra automorphisms $\tau$ of $K_\ell$ such that, for some $\gamma \in \mathrm{SL}_2(\mathbb Z)$ lying in $\Gamma(q) \cap \Gamma_0(M')$, $\tau$ is the level automorphism attached to $\gamma^{-1}$ in the sense of `IsLevelAutAt k₀ q ξ q (q^2*M') H₁ γ⁻¹ Kℓ τ` (its action on quotients $f/g$ of weight-$k$ forms on $\Gamma_{H_1}(q^2M')$ with integral $q$-expansions is substitution by the matrix attached to $\gamma^{-1}$, normalised by $\xi \mapsto e^{2\pi i/q}$), and which stabilises $y$ in the sense that for all $b$ in the chart algebra with $\tau b$ again in the chart algebra one has $b \in y$ if and only if $\tau b \in y$; and $m$ is the number of additive endomorphisms $\iota$ of the group of affine points of $E$ that lie in [`WeierstrassCurve.rationalHomSet (ResidueField ↥A) E E`](def/WeierstrassCurve_RationalEnd.html#L28), admit a two-sided inverse in that same set, and satisfy $\iota(\mathrm{Cyc}) = \mathrm{Cyc}$.
--
--   This is the $q=2$ instance of the comparison, at a supersingular point of the integral model in characteristic $q$, between the order of the stabiliser of that point in the group of level automorphisms coming from $\Gamma(q) \cap \Gamma_0(M')$ and the order of the automorphism group of the corresponding pair $(E, \mathrm{Cyc})$ over the residue field; the explicit factor $2$ on the left reflects that $-1 \in \mathrm{Aut}(E,\mathrm{Cyc})$ acts trivially on the data labelling the point, so the stabiliser has half the order of the automorphism group. The auxiliary level is $\Gamma_1(\ell_g)$-type at the guard prime $\ell_g \equiv 11 \pmod{12}$ dividing $M'$, encoded by $H_1$. It feeds the decomposition-order computation [`ModularCurve.FullLevel.Diamond.two_mul_rigidChart_decompositionOrder_eq_natCard_rationalAut_of_moduliPlace_of_decompositionUnique_linkedScalars_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.Diamond.two_mul_rigidChart_decompositionOrder_eq_natCard_rationalAut_of_moduliPlace_of_decompositionUnique_linkedScalars_of_eq_two_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_two_mul_natCard_levelAut_stabilizer_eq_natCard_rationalAut_of_moduliPlace_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.Diamond.two_mul_natCard_levelAut_stabilizer_eq_natCard_rationalAut_of_moduliPlace_of_eq_two_of_dvd
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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

    2 * Nat.card {τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ //

        (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ) ∧

        (∀ (b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hb : τ (b : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ↔ (⟨τ (b : ↥Kℓ), hb⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y)} =
    Nat.card {ι : E.toAffine.Point →+ E.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet (ResidueField ↥A) E E ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet (ResidueField ↥A) E E, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        Cyc.map ι = Cyc} := by sorry
