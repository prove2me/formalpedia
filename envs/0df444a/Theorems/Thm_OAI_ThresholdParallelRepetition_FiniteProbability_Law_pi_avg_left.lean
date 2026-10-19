-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_FiniteProbability_Law_pi_avg_left
-- name    : OAI.ThresholdParallelRepetition.FiniteProbability.Law.pi_avg_left
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:03:11.685522+00:00
-- url     : https://prove2.me/theorems/bf913db1-43cb-422e-afe5-3e4fc79357b8
-- title:
--   Resampling one first component from its conditional law preserves the i.i.d. product average
-- statement:
--   Let $X$, $Y$ and $I$ be finite sets, let $\mu$ be a probability distribution on $X\times Y$, and let $\rho=\mu^{\otimes I}$ be the product distribution on profiles $z=(z_j)_{j\in I}\in(X\times Y)^I$, so $\rho(z)=\prod_{j\in I}\mu(z_j)$; write $z_j=(x_j,y_j)$. Let $E$ be a real vector space and $f:(X\times Y)^I\to E$ any function. Fix a default point $x_0\in X$. For $y\in Y$ let $\mu(\cdot\mid y)$ be the conditional law of the first component given the second: $\mu(x\mid y)=\mu(x,y)/\mu_Y(y)$ when $\mu_Y(y)=\sum_{x'}\mu(x',y)>0$, and the point mass at $x_0$ when $\mu_Y(y)=0$. For $i\in I$ and $x\in X$ let $z^{x_i\leftarrow x}$ be the profile obtained from $z$ by replacing $x_i$ by $x$ (keeping $y_i$ and all other coordinates), and define the left resampling of coordinate $i$ by
--   $$(\mathcal L_if)(z)=\sum_{x\in X}\mu(x\mid y_i)\,f\bigl(z^{x_i\leftarrow x}\bigr).$$
--   Then for every $i\in I$,
--
--   $$
--   \mathbb{E}_{z\sim\rho}\bigl[(\mathcal L_if)(z)\bigr]=\mathbb{E}_{z\sim\rho}\bigl[f(z)\bigr].
--   $$
--
--   In words: in an i.i.d. sequence of question pairs, redrawing the first component of the $i$-th pair from its conditional distribution given the second component does not change the joint law. On the support of $\rho$, $\mathcal L_if$ is the conditional expectation of $f$ given all coordinates except $x_i$, and the identity is the corresponding tower property. It is the basic invariance used in resampling and exposure arguments for parallel repetition.
--
--   **Formalization Note** Distributions are `Law` structures (finite nonnegative weight vectors summing to $1$) and $\mathbb{E}$ is `Law.avg`, a finite weighted sum. The conditional law is `μ.givenSecond x₀ y`, built with `normalize`, which falls back to the point mass at `x₀` when the column sum vanishes. Profiles are `Profile I X Y = I → X × Y`, $\mathcal L_if$ is `μ.left x₀ i f`, and $E$ is any type with `AddCommMonoid E` and `Module ℝ E`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/Resampling.lean#L144-L159

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

omit [DecidableEq Y] in
theorem OAI.ThresholdParallelRepetition.FiniteProbability.Law.pi_avg_left (μ : Law (X×Y)) (x₀ : X) (i : I) (f : Profile I X Y → E) :
    (pi (fun _ : I => μ)).avg (μ.left x₀ i f) = (pi (fun _ : I => μ)).avg f := by sorry
