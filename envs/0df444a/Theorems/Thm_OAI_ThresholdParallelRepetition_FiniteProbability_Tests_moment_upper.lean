-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_FiniteProbability_Tests_moment_upper
-- name    : OAI.ThresholdParallelRepetition.FiniteProbability.Tests.moment_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:21:42.693471+00:00
-- url     : https://prove2.me/theorems/536ab115-2f45-4e24-855e-6ff4ec7f775b
-- title:
--   Moment bound for the winning rate from a one-step growth inequality
-- statement:
--   Let $\Omega$ be a finite set with a probability law $\rho$ (nonnegative weights $\rho(\omega)$ summing to $1$), let $I$ be a finite nonempty set of coordinates, and let $\mathrm{win}:\Omega\times I\to\{\mathrm{true},\mathrm{false}\}$ indicate which coordinates are won in the outcome $\omega$. For a set $K\subseteq I$ and $t\in\mathbb{N}$ define
--
--   - the event indicator $\mathbf 1_K(\omega)=1$ if $\mathrm{win}(\omega,i)$ holds for every $i\in K$, and $\mathbf 1_K(\omega)=0$ otherwise;
--   - the mass $\mathfrak{m}(K)=\mathbb{E}_{\omega\sim\rho}[\mathbf 1_K(\omega)]$, the probability that all coordinates of $K$ are won;
--   - the winning rate $\mathrm{rate}(\omega)=\frac{1}{|I|}\,\#\{i\in I:\mathrm{win}(\omega,i)\}$;
--   - the moment $\mathfrak{M}(K,t)=\mathbb{E}_{\omega\sim\rho}\bigl[\mathbf 1_K(\omega)\,\mathrm{rate}(\omega)^t\bigr]$.
--
--   Let $r\ge0$, $e\ge0$ and $T\in\mathbb{N}$, and assume that for every $K\subseteq I$ with $|K|<T$
--
--   $$
--   \frac{1}{|I|}\sum_{i\in I}\mathfrak{m}(K\cup\{i\})\le r\,\mathfrak{m}(K)+e .
--   $$
--
--   Then for every $t\in\mathbb{N}$ and every $K\subseteq I$ with $|K|+t\le T$,
--
--   $$
--   \mathfrak{M}(K,t)\le r^t\,\mathfrak{m}(K)+e\sum_{s=0}^{t-1}r^s .
--   $$
--
--   The hypothesis says that adding one uniformly random coordinate to a set of coordinates that must all be won multiplies the probability of winning them all by at most $r$, up to an additive error $e$. The conclusion turns this one-step growth bound into a bound on the conditional moments of the winning rate; with $K=\emptyset$ (so $\mathfrak{m}(\emptyset)=1$) it gives $\mathbb{E}_\rho[\mathrm{rate}^t]\le r^t+e\sum_{s<t}r^s$ for $t\le T$, which together with a Markov-type inequality bounds the probability that the winning rate is large.
--
--   **Formalization Note** The average over $i$ is `(uniform (R := I)).avg` and runs over all of $I$ (for $i\in K$ one has $K\cup\{i\}=K$); $\mathfrak{m}$ and $\mathfrak{M}$ are `mass ρ win` and `moment ρ win`, and the sum $\sum_{s=0}^{t-1}$ is over `Finset.range t`, which is empty for $t=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/TestMoments.lean#L64-L86

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

theorem OAI.ThresholdParallelRepetition.FiniteProbability.Tests.moment_upper {r e : ℝ} (hr : 0 ≤ r) (_he : 0 ≤ e) (T : ℕ)
    (hstep : ∀ c : Finset I, c.card < T →
      (uniform (R := I)).avg (fun i => mass ρ win (insert i c)) ≤ r*mass ρ win c+e) :
    ∀ t : ℕ, ∀ c : Finset I, c.card+t ≤ T →
      moment ρ win c t ≤ r^t*mass ρ win c + e*∑ s ∈ Finset.range t, r^s := by sorry
