-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_FiniteProbability_Law_pi_avg_right
-- name    : OAI.ThresholdParallelRepetition.FiniteProbability.Law.pi_avg_right
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:03:40.167113+00:00
-- url     : https://prove2.me/theorems/fbf0c8c5-7721-4d67-8512-0781f63b2e57
-- title:
--   Resampling one second component from its conditional law preserves the i.i.d. product average
-- statement:
--   Let $X$, $Y$ and $I$ be finite sets, let $\mu$ be a probability distribution on $X\times Y$, and let $\rho=\mu^{\otimes I}$ be the product distribution on profiles $z=(z_j)_{j\in I}\in(X\times Y)^I$, so $\rho(z)=\prod_{j\in I}\mu(z_j)$; write $z_j=(x_j,y_j)$. Let $E$ be a real vector space and $f:(X\times Y)^I\to E$ any function. Fix a default point $y_0\in Y$. For $x\in X$ let $\mu(\cdot\mid x)$ be the conditional law of the second component given the first: $\mu(y\mid x)=\mu(x,y)/\mu_X(x)$ when $\mu_X(x)=\sum_{y'}\mu(x,y')>0$, and the point mass at $y_0$ when $\mu_X(x)=0$. For $i\in I$ and $y\in Y$ let $z^{y_i\leftarrow y}$ be the profile obtained from $z$ by replacing $y_i$ by $y$ (keeping $x_i$ and all other coordinates), and define the right resampling of coordinate $i$ by
--   $$(\mathcal R_if)(z)=\sum_{y\in Y}\mu(y\mid x_i)\,f\bigl(z^{y_i\leftarrow y}\bigr).$$
--   Then for every $i\in I$,
--
--   $$
--   \mathbb{E}_{z\sim\rho}\bigl[(\mathcal R_if)(z)\bigr]=\mathbb{E}_{z\sim\rho}\bigl[f(z)\bigr].
--   $$
--
--   In words: in an i.i.d. sequence of question pairs, redrawing the second component of the $i$-th pair from its conditional distribution given the first component does not change the joint law. On the support of $\rho$, $\mathcal R_if$ is the conditional expectation of $f$ given all coordinates except $y_i$, and the identity is the corresponding tower property. It is the mirror image of the statement for first components and is used in the same resampling and exposure arguments.
--
--   **Formalization Note** Distributions are `Law` structures and $\mathbb{E}$ is `Law.avg`, a finite weighted sum. The conditional law is `μ.givenFirst y₀ x`, built with `normalize`, which falls back to the point mass at `y₀` when the row sum vanishes. Profiles are `Profile I X Y = I → X × Y`, $\mathcal R_if$ is `μ.right y₀ i f`, and $E$ is any type with `AddCommMonoid E` and `Module ℝ E`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/Resampling.lean#L160-L175

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

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.FiniteProbability OAI.ThresholdParallelRepetition.FiniteProbability.Law
universe u_X u_Y u_I u_E u_F u_R
open scoped BigOperators
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {E : Type u_E} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [DecidableEq X] [DecidableEq Y] [AddCommMonoid E] [Module ℝ E]

omit [DecidableEq X] in
theorem OAI.ThresholdParallelRepetition.FiniteProbability.Law.pi_avg_right (μ : Law (X×Y)) (y₀ : Y) (i : I) (f : Profile I X Y → E) :
    (pi (fun _ : I => μ)).avg (μ.right y₀ i f) = (pi (fun _ : I => μ)).avg f := by sorry
