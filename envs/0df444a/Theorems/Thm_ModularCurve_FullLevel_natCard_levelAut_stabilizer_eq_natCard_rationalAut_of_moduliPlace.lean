-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_natCard_levelAut_stabilizer_eq_natCard_rationalAut_of_moduliPlace
-- name    : ModularCurve.FullLevel.natCard_levelAut_stabilizer_eq_natCard_rationalAut_of_moduliPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/ad5706f5-a274-5778-94d5-4b42ca5fa722
-- title:
--   Level-automorphism stabiliser of y counts Aut(E,Cyc)
-- statement:
--   Fix a prime $q\ge 5$ and a positive integer $M'$ with $q\nmid M'$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$. Let $W$ be a finset of places of $\mathrm{modularFunctionFieldC}(\kappa(A),M')$ over $\kappa(A)=\mathrm{ResidueField}\,A$ whose members are exactly the elements of `ssPlaces q M' (ResidueField A)`, that is the rational, affine geometric places whose value at the generator $j$ is a supersingular $j$-invariant in characteristic $q$ (no elliptic curve over the residue field with that $j$ has a nonzero $q$-torsion point), and let $s\in W$. Assume $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a `ConstantReduction` of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with values in $\mathrm{modularFunctionFieldC}(\kappa(A),M')$ (a valuation subring of integers, a surjective residue map with kernel the maximal ideal, compatible with $A$, together with a degree- and order-preserving map on places), whose residue on Laurent series with coefficients in $A$ is coefficientwise reduction. Constants: $k_0\subset\overline{\mathbb{Q}}$ over $\mathbb{Q}$ and $\pi_0\in k_0\cap A$ such that $A\cap k_0$ is a henselian discrete valuation ring with maximal ideal $(\pi_0)$ and algebraically closed residue field, and every element of $A$ is congruent modulo the maximal ideal of $A$ to an element of $k_0\cap A$. Let $\ell'\ge 3$ be a prime, $\ell'\ne q$, $\ell'\nmid M'$, and $\xi\in k_0$ a primitive $q\ell'$-th root of unity. Let $K_\ell$ be the base change to $k_0$ of the $X_H$-function field of level $(q\ell')^2M'$ for $H=\mathrm{levelH}(q\ell')M'$, sitting inside Laurent series over $k_0$, an $(A\cap k_0)$-algebra compatibly with $k_0$, and let $j_\ell\in K_\ell$ be nonzero with Laurent expansion the image of $j_q$. Let $y$ be a maximal ideal of the chart algebra $\mathrm{chartAlgFin}$ of elements of $K_\ell$ integral over $(A\cap k_0)[j_\ell]$, containing the image of $\pi_0$, such that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism from the chart algebra to $\Omega$ with kernel $y$ the image of $j_\ell$ is a supersingular $j$-invariant. Assume further the compatibility `hover`: for every $g$ in the full modular function field of level $M'$ whose base change lies in $R_0$.integers, which has non-negative order at every place of $\mathrm{modularFunctionFieldBar}\,M'$ where $j_q$ does and whose $R_0$-residue lies in the valuation subring of $s$, and for every $c\in k_0\cap A$ whose residue in $\kappa(A)$ is the value of $s$ at that $R_0$-residue, the chart element given by $\mathrm{qExpand}_{\ell'}$ of $g$ minus the image of $c$ lies in $y$. Finally let $E$ be an elliptic Weierstrass curve over $\kappa(A)$ and $\mathrm{Cyc}$ a cyclic subgroup of $E(\kappa(A))$ of cardinality $M'$ such that the valuation subring of $s$ is the pullback of that of $\mathrm{moduliPlace}(\kappa(A),M',E,\mathrm{Cyc})$ along the inclusion of $\mathrm{modularFunctionFieldC}$ into $\mathrm{modularFunctionFieldFullC}$. Then the number of $k_0$-algebra automorphisms $\tau$ of $K_\ell$ such that (i) there is $\gamma\in SL(2,\mathbb{Z})$ with $\gamma\in\Gamma(q)$, $\gamma\in\Gamma_0(M')$ and `IsLevelAutAt` holds for $\gamma^{-1}$ and $\tau$ (for all weight-$k$ forms $f,g$ on $\Gamma_H((q\ell')^2M')$ with integral $q$-expansions and $g\ne 0$, and all $x\in K_\ell$ expanding as $f/g$, every embedding of $k_0$ into $\mathbb{C}$ sending $\xi$ to $e^{2\pi i/(q\ell')}$ carries $\tau x$ to the ratio of the $q$-expansions of $f$ and $g$ acted on by $\mathrm{conjElemN}(q\ell')\gamma^{-1}$), and (ii) $\tau$ preserves $y$, in the sense that for every $b$ in the chart algebra with $\tau b$ again in it one has $b\in y$ if and only if $\tau b\in y$, equals the number of additive endomorphisms $\iota$ of $E(\kappa(A))$ which lie in $\mathrm{rationalHomSet}$ (zero or rationally represented), admit a two-sided inverse in $\mathrm{rationalHomSet}$, and satisfy $\iota(\mathrm{Cyc})=\mathrm{Cyc}$.
--
--   This is the moduli-theoretic identification of the stabiliser, inside the deck group of level automorphisms attached to $\Gamma(q)\cap\Gamma_0(M')$, of a supersingular point $y$ of the integral chart at level $q\ell'$: its order is the order of the automorphism group of the corresponding pair $(E,\mathrm{Cyc})$ over the residue field, with $-1$ counted. It feeds the computation of the decomposition order at a rigid chart point used in the ramification analysis of the modular curve in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_natCard_levelAut_stabilizer_eq_natCard_rationalAut_of_moduliPlace.lean

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

open AlgebraicCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open ModularCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.natCard_levelAut_stabilizer_eq_natCard_rationalAut_of_moduliPlace
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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

    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'3 : 3 ≤ ℓ') (hℓ'q : ℓ' ≠ q) (hℓ'M : ¬ ℓ' ∣ M')
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓ'))

    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
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
      ∀ (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ Kℓ)
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

        (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ) ∧

        (∀ (b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hb : τ (b : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ↔ (⟨τ (b : ↥Kℓ), hb⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y)} =
    Nat.card {ι : E.toAffine.Point →+ E.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet (ResidueField ↥A) E E ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet (ResidueField ↥A) E E, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        Cyc.map ι = Cyc} := by sorry
