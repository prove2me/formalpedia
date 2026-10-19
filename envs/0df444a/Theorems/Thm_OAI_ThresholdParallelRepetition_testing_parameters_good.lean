-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_testing_parameters_good
-- name    : OAI.ThresholdParallelRepetition.testing_parameters_good
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:28:26.006804+00:00
-- url     : https://prove2.me/theorems/308d842e-c6a6-4889-9c74-8edcf8ea3785
-- title:
--   Parameter inequalities that enable the conditioned one-step bound
-- statement:
--   Let $\delta,k,d,p$ be real numbers and $c$ a natural number such that $0<\delta\le1$, $k>0$, $d\ge1$ and
--
--   $$
--   c\le\frac{\delta^9k}{2^{90}\,(1+\log d)},\qquad p\ge\exp\Bigl(-\frac{\delta^8k}{2^{83}}\Bigr),
--   $$
--
--   where $\log$ is the natural logarithm. Then
--
--   $$
--   c\le\frac{\delta k}{4},\qquad c<k,\qquad\frac{\log(d^c/p)}{k-c}\le\frac{\delta^8}{2^{80}} .
--   $$
--
--   In the parallel-repetition argument, $k$ is the number of coordinates, $d=(a+1)(b+1)$ the number of answer pairs per coordinate, $c$ the size of a set $K$ of coordinates that are conditioned to be won, and $p$ the probability of winning all of them. The lemma says that as long as $|K|$ stays below the threshold $\delta^9k/(2^{90}(1+\log d))$ and the conditioning event has probability at least $e^{-\delta^8k/2^{83}}$, the size and entropy hypotheses of the conditioned one-step bound are satisfied.
--
--   **Formalization Note** The natural number $c$ is cast to a real number, $d^c$ is a natural-number power, and positivity of $p$ (so that the logarithm is applied to a positive number) and of $k-c$ follow from the hypotheses.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/ConditionedStep.lean#L105-L137

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

open OAI OAI.ThresholdParallelRepetition
universe u_I

theorem OAI.ThresholdParallelRepetition.testing_parameters_good {δ k d p : ℝ} {c : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < k) (hd : 1 ≤ d)
    (hc : (c : ℝ) ≤ δ^9*k/((2:ℝ)^90*(1+Real.log d)))
    (hp : Real.exp (-(δ^8*k/(2:ℝ)^83)) ≤ p) :
    (c : ℝ) ≤ δ*k/4 ∧ (c : ℝ) < k ∧
      Real.log (d^c/p)/(k-(c : ℝ)) ≤ δ^8/(2:ℝ)^80 := by sorry
