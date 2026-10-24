-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_itoFormula_localise_408915f
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_localise_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:40:37.658556+00:00
-- url     : https://prove2.me/theorems/ac60cb22-b182-4e0f-bbc3-5a45efef071c
-- title:
--   Localization Step for Vector Itô Formula
-- statement:
--   This is the localization step extending a bounded-derivative vector Itô formula to a twice continuously differentiable function.
--
--   Let $(\Omega,\mathcal A,P)$ be a probability space, let $W$ be a $d$-dimensional Brownian motion, let $\mathcal F$ be a filtration, and let $X$ be an $n$-dimensional vector Itô process with initial value $X_0$, drift $b^{\mathrm{drift}}$, and diffusion coefficients $H_{p,k}$. Assume `h` states that these data form an `IsVectorItoVersion`, including the coordinate Brownian-filtration hypotheses, joint measurability, progressive measurability, and finite `ENNReal` energy of every $H_{p,k}$. Let $f:(\operatorname{Fin}(n)\to\mathbb R)\to\mathbb R$ be $C^2$, with first and second derivative fields $f'$ and $f''$ satisfying the stated `HasFDerivAt` hypotheses. Assume also that every product of a coordinate derivative of $f'$ with $H_{p,k}$ is measurable, progressively measurable, and has finite energy on every positive horizon.
--
--   In addition, assume the bounded-derivative formula `hbase`: for every twice differentiable test function $g$ with derivative bounds $\|g'(z)\|\le K_1$, $0\le K_2$, second-derivative bounds $\|g''(z)\|\le K_2$, continuous derivative fields, and the stated uniform continuity condition on $g''$, the corresponding formula holds whenever its coordinate stochastic integrands satisfy the analogous measurability, progressive-measurability, and finite-energy hypotheses.
--
--   Then, for every $T>0$, $P$-almost everywhere,
--   $$
--   \begin{aligned}
--   f(X_T)-f(X_0)
--   ={}&\sum_{p}\int_{(0,T]} \partial_p f(X_s)b^{\mathrm{drift}}_p(s)\,ds\\
--   &+\sum_{p,j} I_T\!\left[s\mapsto \partial_p f(X_s)H_{p,j}(s)\right]\\
--   &+\frac12\sum_{p,q}\int_{(0,T]}\partial_{pq}f(X_s)\left(\sum_j H_{p,j}(s)H_{q,j}(s)\right)ds.
--   \end{aligned}
--   $$
--   Here the stochastic integrals are the coordinate Brownian integrals appearing in the type, and all sums range over the corresponding finite index types.
--
--   The theorem is the localization component needed for the full $C^2$ vector Itô formula: it removes global boundedness assumptions on the first and second derivatives while retaining all stated integrability conditions.
--
--   **Formalization Note.** `coordDeriv` and `coordDeriv₂` denote coordinate first and second derivatives. The formula is an almost-everywhere equality under $P$, uses Lebesgue set integrals over $(0,T]$, and retains the explicit factor $1/2$.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoCutoff.lean#L313-L511 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoCutoff`, declaration `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_localise`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Algebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_DenseCountable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_ENNReal
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_FiniteInf
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LinearAlgebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeanInequalities
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeasureTheory
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Metric
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Nat
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Topology
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_Chaining
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_CoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_IsKolmogorovProcess
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsov
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsovInequality
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_LimitModification
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_BrownianMotion
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_Moment
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_ProjectiveLimit
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_StochasticProcesses
import Definitions.Def_KLS408915f_KolmogorovExtension4_CompactSystem
import Definitions.Def_KLS408915f_KolmogorovExtension4_KolmogorovExtension
import Definitions.Def_KLS408915f_KolmogorovExtension4_RegularContent
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_AugmentedFiltration
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CoordDerivative
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossVariation
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossVariationSum
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Existence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraProduct
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoCutoff
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityDyadicAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPredictableL2
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityShiftedAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityUnbounded
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFormulaGrid
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFourthMomentLintegral
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoIncrementMomentRestrict
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionApi
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionConvergence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionExistence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionLp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoLocality
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoMartingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoOptionalStopping
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoPullOut
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoQuadVarSum
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimFiltered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_PolarisedQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SmoothCutoff
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_TaylorTwoVector
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoFormula
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcess
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Augmentation
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ExitTime
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_StoppedProgressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.EMetricSpace.PairReduction
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoCutoff.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open scoped Topology
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u
section Formula
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)

theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_localise_408915f
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hbase : ∀ (g : (Fin n → ℝ) → ℝ) (g' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ)
      (g'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (K₁ K₂ : ℝ),
      (∀ z, HasFDerivAt g (g' z) z) → (∀ z, HasFDerivAt g' (g'' z) z) →
      (∀ z, ‖g' z‖ ≤ K₁) → 0 ≤ K₂ → (∀ z, ‖g'' z‖ ≤ K₂) →
      Continuous g' → Continuous g'' →
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ z w : Fin n → ℝ, ‖z - w‖ < δ → ‖g'' z - g'' w‖ ≤ ε) →
      ∀ (hmG : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
          fun ω s => coordDeriv g' p (X s ω) * H p k ω s))
        (hpG : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
          fun ω s => coordDeriv g' p (X s ω) * H p k ω s)
        (hqG : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
            (‖coordDeriv g' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      (fun ω : Ω => g (X T ω) - g (X 0 ω)) =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv g' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv g' p (X s ω) * H p k ω s)
              (hmG p k) (hpG p k) (hqG p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ g'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
            (hmg p j) (hpg p j) (hqg p j) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume := by sorry
