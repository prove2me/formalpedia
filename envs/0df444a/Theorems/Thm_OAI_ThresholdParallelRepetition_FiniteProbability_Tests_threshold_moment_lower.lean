-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_FiniteProbability_Tests_threshold_moment_lower
-- name    : OAI.ThresholdParallelRepetition.FiniteProbability.Tests.threshold_moment_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:23:30.600234+00:00
-- url     : https://prove2.me/theorems/4a6f86a6-12d1-48e4-87bf-e079780d6d06
-- title:
--   Markov-type inequality for moments of the winning rate
-- statement:
--   Let $\Omega$ be a finite set with a probability law $\rho$ (nonnegative weights $\rho(\omega)$ summing to $1$), let $I$ be a finite nonempty set of coordinates, and let $\mathrm{win}:\Omega\times I\to\{\mathrm{true},\mathrm{false}\}$ indicate which coordinates are won in the outcome $\omega$. Define the winning rate $\mathrm{rate}(\omega)=\frac{1}{|I|}\,\#\{i\in I:\mathrm{win}(\omega,i)\}\in[0,1]$ and, for $t\in\mathbb{N}$, the moment $\mathfrak{M}(\emptyset,t)=\mathbb{E}_{\omega\sim\rho}\bigl[\mathbf 1_\emptyset(\omega)\,\mathrm{rate}(\omega)^t\bigr]$, where $\mathbf 1_\emptyset\equiv1$ is the indicator that all coordinates of the empty set are won; thus $\mathfrak{M}(\emptyset,t)=\mathbb{E}_\rho[\mathrm{rate}^t]$.
--
--   For every real $q\ge0$ and every $t\in\mathbb{N}$,
--
--   $$
--   \Pr_{\omega\sim\rho}\bigl[\mathrm{rate}(\omega)\ge q\bigr]\cdot q^t\le\mathfrak{M}(\emptyset,t)=\mathbb{E}_{\omega\sim\rho}\bigl[\mathrm{rate}(\omega)^t\bigr].
--   $$
--
--   This is Markov's inequality for the nonnegative random variable $\mathrm{rate}^t$. It converts an upper bound on the $t$-th moment of the winning rate into an upper bound on the probability that the rate reaches the threshold $q$, which is how the tail of the number of won coordinates is controlled in parallel repetition.
--
--   **Formalization Note** The probability is the expectation `ρ.avg (fun ω => if q ≤ rate win ω then 1 else 0)` of an indicator, and $\mathfrak{M}(\emptyset,t)$ is `moment ρ win ∅ t`. For $t=0$ the convention $0^0=1$ applies and the statement says that the probability is at most $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/TestMoments.lean#L88-L102

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
import Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Resampling
import Definitions.Def_OAI_Probability_EntangledGames_EffectExposure
import Definitions.Def_OAI_Probability_EntangledGames_ExposureChain
import Definitions.Def_OAI_Probability_EntangledGames_BlockStates
import Definitions.Def_OAI_Probability_EntangledGames_FreshStates
import Definitions.Def_OAI_Probability_EntangledGames_ExposureData
import Definitions.Def_OAI_Probability_EntangledGames_Refinement
import Definitions.Def_OAI_Probability_EntangledGames_ExposureErrors
import Definitions.Def_OAI_Probability_EntangledGames_Rounding
import Definitions.Def_OAI_Probability_EntangledGames_RepeatedModel
import Definitions.Def_OAI_Probability_EntangledGames_TestMoments

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.FiniteProbability OAI.ThresholdParallelRepetition.FiniteProbability.Tests
universe u_I u_Ω
open scoped BigOperators
open Law
variable {I : Type u_I} {Ω : Type u_Ω} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]
  (ρ : Law Ω) (win : Ω → I → Bool)

theorem OAI.ThresholdParallelRepetition.FiniteProbability.Tests.threshold_moment_lower {q : ℝ} (hq : 0 ≤ q) (t : ℕ) :
    (ρ.avg (fun ω => if q ≤ rate win ω then (1:ℝ) else 0))*q^t ≤ moment ρ win ∅ t := by sorry
