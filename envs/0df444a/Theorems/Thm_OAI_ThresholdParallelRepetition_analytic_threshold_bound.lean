-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_analytic_threshold_bound
-- name    : OAI.ThresholdParallelRepetition.analytic_threshold_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:29:16.274699+00:00
-- url     : https://prove2.me/theorems/64832475-0a1c-4f9d-af22-e2b66d3093e3
-- title:
--   Exponential tail bound from a power-weighted threshold inequality
-- statement:
--   Let $v,\delta,\theta,R,E,q$ be real numbers and let $T=\lfloor\theta\rfloor$ be the integer part of $\theta$. Assume
--
--   - $v\ge0$, $0<\delta\le1$ and $v+\delta\le1$;
--   - $\theta\ge2$ and $\delta\theta\ge8$;
--   - $\theta/\delta\le R/4$ and $2/\delta\le R/4$;
--   - $E\le\delta\theta/8$;
--
--   and assume that $q$ satisfies
--
--   $$
--   q\,(v+\delta)^T\le\Bigl(v+\frac\delta2\Bigr)^T+\frac2\delta\,e^{-R}.
--   $$
--
--   Then
--
--   $$
--   q\le e^{-E}.
--   $$
--
--   In the threshold parallel-repetition argument, $v$ is the entangled value of the game, $q$ is the probability that the fraction of won coordinates reaches $v+\delta$, and the hypothesis on $q$ is the form obtained by combining Markov's inequality for the $T$-th moment of the winning rate with an upper bound on that moment. The lemma isolates the purely analytic step that turns this moment estimate into an exponential tail bound.
--
--   **Formalization Note** $T$ is the natural-number floor `⌊θ⌋₊`; no sign condition is imposed on $q$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/ExponentialBounds.lean#L44-L99

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
import Definitions.Def_OAI_Probability_EntangledGames_TestExtraction

open OAI OAI.ThresholdParallelRepetition

theorem OAI.ThresholdParallelRepetition.analytic_threshold_bound {v δ θ R E q : ℝ}
    (hv : 0 ≤ v) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : v+δ ≤ 1)
    (hθ : 2 ≤ θ) (hδθ : 8 ≤ δ*θ)
    (hθR : θ/δ ≤ R/4) (hR : 2/δ ≤ R/4) (hE : E ≤ δ*θ/8)
    (hq : q*(v+δ)^(⌊θ⌋₊) ≤ (v+δ/2)^(⌊θ⌋₊)+Real.exp (-R)*(2/δ)) :
    q ≤ Real.exp (-E) := by sorry
