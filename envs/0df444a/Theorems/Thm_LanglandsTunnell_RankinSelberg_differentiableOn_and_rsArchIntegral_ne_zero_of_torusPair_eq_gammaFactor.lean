-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_differentiableOn_and_rsArchIntegral_ne_zero_of_torusPair_eq_gammaFactor
-- name    : LanglandsTunnell.RankinSelberg.differentiableOn_and_rsArchIntegral_ne_zero_of_torusPair_eq_gammaFactor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/ff37a771-628f-53fc-82a7-ffefbf501e68
-- title:
--   Archimedean holomorphy and non-vanishing from a torus Γ-factor identity
-- statement:
--   Let $W_A\colon \mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$ and $W_F\colon \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q},\infty})\to\mathbb{C}$ be functions, and write $g\mapsto \Phi(g)$ for the map $\mathrm{GL}_2(\mathbb{R})\to\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q},\infty})$ obtained by embedding $g$ into the adelic $\mathrm{GL}_2$ over $\mathbb{Q}$ at the real place via `archRealGLAt`, applying the cubic inclusion `iota` into the adelic $\mathrm{GL}_3$, and taking its archimedean component. Assume: the product $q\mapsto W_A(q)\,W_F(\Phi(q))$ is invariant under left multiplication by elements of the image of `unipotentGL2Hom` over $\mathbb{R}$ and under right multiplication by elements $k$ of the row-isometry subgroup of $\mathrm{GL}_2(\mathbb{R})$ with $\det k = 1$; and, for multisets $\Gamma_{\mathbb{R}},\Gamma_{\mathbb{C}}$ of complex shifts, a real $\sigma_a$ and $e\neq 0$, the torus identity $$\int_{a_2>0}\int_{a_1\in\mathbb{R}} W_A(q)\,W_F(\Phi(q))\,|\det q|^{\,s-1/2}\,a_1^{-2}\,da_1\,da_2 \;=\; e\prod_{x\in\Gamma_{\mathbb{R}}}\Gamma_{\mathbb{R}}(s+\tfrac12+x)\prod_{x\in\Gamma_{\mathbb{C}}}\Gamma_{\mathbb{C}}(s+\tfrac12+x)$$ holds for $\operatorname{Re} s>\sigma_a$, where $q=\operatorname{diag}(a_1,a_2)$ (the integrand being set to $0$ unless $a_1\neq 0$ and $a_2>0$). Equip $\mathrm{GL}_2(\mathbb{R})$ with its Borel $\sigma$-algebra and assume further that $W_A$ and $g\mapsto W_F(\Phi(g))$ are measurable and that for every Haar measure $\mu_N$ on the unipotent subgroup there is $\sigma_I$ with $g\mapsto W_A(g)W_F(\Phi(g))|\det g|^{s-1/2}$ integrable against [`RSCarrier.archMeasure`](def/LanglandsTunnell_RSCarrierSplit.html#L11) weighted by the orbit density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of $\mu_N$, for $\operatorname{Re} s>\sigma_I$. Then for every Haar measure $\mu_{NA}$ on that unipotent subgroup there exist $h_A\in \mathrm{GL}_2(\mathbb{R})$, $h_{A,3}\in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q},\infty})$ and $\sigma\in\mathbb{R}$ such that the Rankin–Selberg archimedean integral [`RSCarrier.rsArchIntegral`](def/LanglandsTunnell_RSCarrier.html#L27) of the translated pair $M\mapsto |\det M|^{-1/2}W_A(Mh_A)$, $M\mapsto W_F(\Phi(M)h_{A,3})$, taken with respect to [`RSCarrier.archMeasure`](def/LanglandsTunnell_RSCarrierSplit.html#L11) and $\mu_{NA}$, is differentiable on $\{\operatorname{Re} s>\sigma\}$ and non-zero at some $s$ with $\operatorname{Re} s>\sigma$.
--
--   This is the archimedean input of the $\mathrm{GL}_3\times\mathrm{GL}_2$ Rankin–Selberg theory used in the converse-theorem route to Langlands–Tunnell: a torus-coordinate evaluation of the Whittaker pairing as a non-zero constant times a product of $\Gamma$-factors is converted into holomorphy of the archimedean local integral in a right half-plane together with non-vanishing somewhere there, for a suitable pair of translates. It discharges the archimedean hypothesis threaded through the global Rankin–Selberg $L$-function statement [`LanglandsTunnell.RankinSelberg.exists_entire_boundedOnStrips_eq_archFactor_mul_lFun_rsDatum_of_le_conductorExponentAt_of_centralInduced_of_localSpaceAt_of_normPin_archTrivial`](thm.html#LanglandsTunnell.RankinSelberg.exists_entire_boundedOnStrips_eq_archFactor_mul_lFun_rsDatum_of_le_conductorExponentAt_of_centralInduced_of_localSpaceAt_of_normPin_archTrivial), and relies on the torus-identity lemma [`LanglandsTunnell.Converse.exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities`](thm.html#LanglandsTunnell.Converse.exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities) together with the Haar property of [`RSCarrier.archMeasure`](def/LanglandsTunnell_RSCarrierSplit.html#L11).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_differentiableOn_and_rsArchIntegral_ne_zero_of_torusPair_eq_gammaFactor.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.differentiableOn_and_rsArchIntegral_ne_zero_of_torusPair_eq_gammaFactor
    (WA : GL (Fin 2) ℝ → ℂ) (WF : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (_hN : ∀ n ∈ RSCarrier.realUnipotent, ∀ q : GL (Fin 2) ℝ,
      WA (n * q) * WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (n * q))))
        = WA q * WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q))))
    (_hK : ∀ k ∈ AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 → ∀ q : GL (Fin 2) ℝ,
      WA (q * k) * WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (q * k))))
        = WA q * WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q))))
    (ΓR ΓC : Multiset ℂ) (σa : ℝ) (e : ℂ) (_he : e ≠ 0)
    (_hT : ∀ s : ℂ, σa < s.re →
      (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
        if ha : a₁ ≠ 0 ∧ 0 < a₂ then
          let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
          ((WA q * WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
            (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
        else 0)
        = e * ((ΓR.map fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
            (ΓC.map fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod)) :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (_hW : Measurable WA)
      (_hF : Measurable fun g : GL (Fin 2) ℝ => WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g))))
      (_hint : ∀ (μN : Measure RSCarrier.realUnipotent) [μN.IsHaarMeasure], ∃ σI : ℝ,
        ∀ s : ℂ, σI < s.re → MeasureTheory.Integrable
          (fun g : GL (Fin 2) ℝ =>
            (WA g * WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g)))) *
              (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
          (RSCarrier.archMeasure.withDensity (HaarQuotient.density RSCarrier.realUnipotent μN))),
    ∀ (μNA : Measure RSCarrier.realUnipotent) [μNA.IsHaarMeasure],
      ∃ (hA : GL (Fin 2) ℝ) (hA3 : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : ℝ),
        DifferentiableOn ℂ
            (fun s : ℂ => RSCarrier.rsArchIntegral RSCarrier.archMeasure μNA s
              (fun M : GL (Fin 2) ℝ => ((((|(Matrix.GeneralLinearGroup.det M : ℝ)| : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) * WA (M * hA)))
              (fun M : GL (Fin 2) ℝ => WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M)) * hA3)))
            {s : ℂ | σ < s.re} ∧
        ∃ s : ℂ, σ < s.re ∧
          RSCarrier.rsArchIntegral RSCarrier.archMeasure μNA s
              (fun M : GL (Fin 2) ℝ => ((((|(Matrix.GeneralLinearGroup.det M : ℝ)| : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) * WA (M * hA)))
              (fun M : GL (Fin 2) ℝ => WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M)) * hA3)) ≠ 0 := by sorry
