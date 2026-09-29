-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_residuallyTranscendental_trace_of_igusaBranch_of_rigidChart
-- name    : ModularCurve.FullLevel.exists_residuallyTranscendental_trace_of_igusaBranch_of_rigidChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/34ff1de4-fc97-5cf4-a9bb-619eb3760f9c
-- title:
--   Residually transcendental trace along an Igusa branch
-- statement:
--   Fix a prime $q\ge 5$, a non-zero $M'$ with $q\nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')=\mathrm{ResidueField}\,A(j(\mathsf q),j(\mathsf q^{M'}))$ whose members are exactly the supersingular places `ssPlaces q M'` (rational, affine geometric, with value of the geometric $j$ in `ssJSet q`, the set of $j$ for which every elliptic curve with that invariant has no non-trivial $q$-torsion point), let $s\in W$, and let $R_0$ be a `ConstantReduction` of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to that field, assumed to reduce every Laurent series with coefficients in $A$ lying in $\mathrm{modularFunctionFieldBar}\,M'$ coefficientwise. Let $k_0\subseteq\overline{\mathbb Q}$ with $\pi_0\in k_0\cap A$, such that $A\cap k_0$ is a discrete valuation ring with maximal ideal $(\pi_0)$; let $\ell'\ge 3$ be a prime, $\ell'\ne q$, $\ell'\nmid M'$, and let $K_\ell$ be the base change to $k_0$ of the $X_H$ function field of level $(q\ell')^2M'$ for $H=\mathrm{levelH}(q\ell')M'$, with $j_\ell\in K_\ell$ non-zero of $q$-expansion $j(\mathsf q)$, and with the evident algebra and scalar-tower structure over $A\cap k_0$. Let $y$ be a maximal ideal of the chart algebra $\mathrm{chartAlgFin}(A\cap k_0)K_\ell\,j_\ell$ (elements integral over $(A\cap k_0)[j_\ell]$) containing $\pi_0$ and such that every homomorphism of that algebra onto an algebraically closed field of characteristic $q$ with kernel $y$ carries $j_\ell$ into `ssJSet q`. Assume further: the compatibility `hover` between $y$ and the place $s$ for functions of level $M'$ regular where $j$ is; that $j(\mathsf q^{q\ell'})$ lies in $K_\ell$, in the chart algebra, and is congruent modulo $y$ to some $a_0\in A\cap k_0$; that $\xi\in k_0$ is a primitive $(q\ell')$-th root of unity; that $G\le\mathrm{Aut}(K_\ell/k_0)$ consists of automorphisms realised, via `IsLevelAutAt`, by $\gamma^{-1}$ for $\gamma\in\Gamma(q)\cap\Gamma_0(M')$, with $K_0$ the fixed field of $G$; and that $\tilde O\subseteq W_x$ for a valuation subring $W_x$ of $K_\ell$ which is a discrete valuation ring containing the chart algebra, meets $k_0$ exactly in $A\cap k_0$, whose maximal ideal pulls chart elements into $y$ while some element of $y$ stays a unit, and for which $j(\mathsf q^{q\ell'})$ is residually transcendental over $A\cap k_0$ (a polynomial over $A\cap k_0$ whose value there lies in the maximal ideal of $W_x$ has all coefficients in the maximal ideal of $A\cap k_0$). The conclusion: there is $t\in W_x\cap K_0$ which is residually transcendental over $A$, namely for every $p\in k_0[X]$ all of whose coefficients lie in $A$, if $p(t)$ lies in the maximal ideal of $W_x\cap K_0$ then every coefficient of $p$ lies in $W_x\cap K_0$ and in its maximal ideal.
--
--   This is the descent step for Igusa-type branches: the residual transcendence of the moduli parameter $j(\mathsf q^{q\ell'})$ on the auxiliary level-$(q\ell')$ curve is transported to its image on the quotient by the deck group $G$, producing a residually transcendental element of the valuation ring induced on the fixed field $K_0$. It is used by [`ModularCurve.FullLevel.pernodeConclusion_traces_of_rigidDescentHyps`](thm.html#ModularCurve.FullLevel.pernodeConclusion_traces_of_rigidDescentHyps) in the analysis of the supersingular nodes of the full-level model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_residuallyTranscendental_trace_of_igusaBranch_of_rigidChart.lean

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
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 12800000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_residuallyTranscendental_trace_of_igusaBranch_of_rigidChart
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
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
    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'3 : 3 ≤ ℓ') (hℓ'q : ℓ' ≠ q) (hℓ'M : ¬ ℓ' ∣ M')
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
    (hjK : ModularCurve.jqNModC ↥k₀ (q * ℓ') ∈ Kℓ)
    (hjC : (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha₀y : (⟨(⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ), hjC⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) a₀ ∈ y)
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓ'))
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ))
    (hGatt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ)
    (K₀ : IntermediateField ↥k₀ ↥Kℓ) (hK₀ : K₀ = IntermediateField.fixedField G)
    (Õ : Subring ↥Kℓ)
    (Wx : ValuationSubring ↥Kℓ)
    (hOWx : ∀ f : ↥Kℓ, f ∈ Õ → f ∈ Wx)
    (hWxdvr : IsDiscreteValuationRing ↥Wx)
    (hCWx : ∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx)
    (hVA : ∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wx ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x)
    (hcentre : ∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y)
    (hne : ∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx)
    (hVj : ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
      (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ (q * ℓ'), hjK⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
        ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) :
    ∃ t : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ)), ∀ p : Polynomial ↥k₀, (∀ i, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
        (∃ hm : Polynomial.aeval (t : ↥K₀) p ∈ Wx.comap (algebraMap ↥K₀ ↥Kℓ), (⟨_, hm⟩ : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) ∈ maximalIdeal ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) →
          ∀ i, ∃ hc : algebraMap ↥k₀ ↥K₀ (p.coeff i) ∈ Wx.comap (algebraMap ↥K₀ ↥Kℓ), (⟨_, hc⟩ : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) ∈ maximalIdeal ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ)) := by sorry
