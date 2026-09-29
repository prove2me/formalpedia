-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_levelAut_sub_self_mem_of_isLevelAutAt_of_mem_Gamma_of_over_ssPlace_rigidDataPow
-- name    : ModularCurve.FullLevel.levelAut_sub_self_mem_of_isLevelAutAt_of_mem_Gamma_of_over_ssPlace_rigidDataPow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/16871107-59b1-51bc-9c56-c311415ad000
-- title:
--   Level automorphisms in Γ(ℓ')∩Γ₀(M') fix supersingular closed points
-- statement:
--   Fix a prime $q\ge 5$ and a positive integer $M'$ with $q\nmid M'$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, a finset $W$ consisting exactly of the supersingular places in `ssPlaces q M' (ResidueField A)` of `modularFunctionFieldC (ResidueField A) M'`, an inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'`, a constant reduction $R_0$ of `modularFunctionFieldBar M'` along $A$ with values in `modularFunctionFieldC (ResidueField A) M'` whose residue map is compatible, via `hR₀`, with coefficientwise reduction of Laurent series over $A$, and a chosen $s\in W$. Fix further a subfield $k_0\subseteq\overline{\mathbb{Q}}$ and $\pi_0\in k_0\cap A$ such that $A_0:=A\cap k_0$ is a henselian discrete valuation ring with maximal ideal $(\pi_0)$ and algebraically closed residue field, every element of $A$ being congruent modulo the maximal ideal of $A$ to an element of $k_0\cap A$; an auxiliary prime $\ell'\ne q$ with $\ell'\ge 3$ and $\ell'\nmid M'$; a primitive $(q\ell')$-th root of unity $\xi\in k_0$ admitting an embedding $k_0\to\mathbb{C}$ sending it to $e^{2\pi i/(q\ell')}$; $K$ the base change to $k_0$ of the function field of the $H$-level curve `xHFunctionField ((q*ℓ')^2*M') (levelH (q*ℓ') M')`, an $A_0$-algebra in a scalar tower, and $j\in K$ nonzero with Laurent expansion the image of `jq`. Hypotheses `hℓ`, `hM`, and the data $\mathcal{G}$ chord-tangent and origin-normalised, $\mathcal{T}$ a section-transporting level transport at $q$, together with `hVC`, `hCO` (graded realisations of variable changes and of coefficient homomorphisms on projective models) are summarised here as the moduli frame over $A_0$. Write $C'$ for the chart algebra `chartAlgFin A₀ K j` of elements integral over $A_0[j]$. The conclusion: let $\gamma\in SL_2(\mathbb{Z})$ lie in $\Gamma(\ell')\cap\Gamma_0(M')$, let $\tau$ be a $k_0$-algebra automorphism of $K$ which is a level automorphism at $\gamma^{-1}$ in the sense of `IsLevelAutAt` (for all weights $k$ and all pairs of modular forms $f,g$ for $\Gamma_H((q\ell')^2M')$ with integral $q$-expansions, $g\ne 0$, and all $x\in K$ whose expansion is the quotient of their expansions, the image $\tau x$ has, under any embedding $k_0\to\mathbb{C}$ normalising $\xi$, the $q$-expansion of $f\mid_k\gamma$ divided by that of $g\mid_k\gamma$, with $\gamma$ acting through `conjElemN (q*ℓ')`), suppose $\tau$ maps $C'$ into itself, and let $y'$ be a maximal ideal of $C'$ containing the image of $\pi_0$ which lies over $s$ in the following sense: for every $g$ in the full modular function field of level $M'$ over $\mathbb{Q}$ whose image in `modularFunctionFieldBar M'` lies in $R_0$'s valuation subring, is nonnegatively valued at every place of that field at which the image of `jq` is, and has $R_0$-residue in the valuation subring of $s$, and for every $c\in k_0\cap A$ whose residue in the residue field of $A$ is the value at $s$ of that $R_0$-residue, the element `qExpand k₀ ℓ' (coeffEmb k₀ g)` of $K$, whenever it lies in $C'$, differs from the image of $c$ by an element of $y'$. Then $\tau(b)-b\in y'$ for every $b\in C'$.
--
--   This is the statement that a level automorphism attached to $\gamma\equiv 1 \pmod{\ell'}$, $\gamma\in\Gamma_0(M')$, induces the identity on the residue field at a closed point of the special fibre of the $j$-finite chart lying over a supersingular place, i.e. that such automorphisms fix the supersingular points of the reduction. It is obtained from the supersingular fibre dictionary together with the invariance of a supersingular full-level structure under relabelling by $\gamma$, and is used in the analysis of the local behaviour of the level field at supersingular points of $X_H$ in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_levelAut_sub_self_mem_of_isLevelAutAt_of_mem_Gamma_of_over_ssPlace_rigidDataPow.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.levelAut_sub_self_mem_of_isLevelAutAt_of_mem_Gamma_of_over_ssPlace_rigidDataPow
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

    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'q : ℓ' ≠ q) (hℓ'3 : 3 ≤ ℓ') (hℓ'M' : ¬ ℓ' ∣ M')
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓ'))
    (hιξ : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')))
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ' D →
        ModularCurve.IsLevelPStructure (C • W) ℓ' (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] [CommRing T'] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T'] (f : T →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ) :
    ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma ℓ' → γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ (τ : ↥K ≃ₐ[↥k₀] ↥K),
        ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ K τ →
        ∀ (hpres : ∀ f : ↥K, f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j → τ f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)
          (y' : {y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) // y.IsMaximal ∧ algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨π₀, hπ⟩ ∈ y}),

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
          ∀ (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ K)
            (hgC : (⟨_, hgK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
          ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
            residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
            (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨c, hc⟩ ∈ y'.1) →
          ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
            (⟨τ (b : ↥K), hpres _ b.2⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) - b ∈ y'.1 := by sorry
