-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_RepeatedModel_unconditional_rate_le_value
-- name    : OAI.ThresholdParallelRepetition.RepeatedModel.unconditional_rate_le_value
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:27:42.192762+00:00
-- url     : https://prove2.me/theorems/909057f0-bc1c-43f9-ad27-2c064294c996
-- title:
--   The expected fraction of won coordinates is at most the entangled value
-- statement:
--   Let $G$ be a two-player nonlocal game with question sets $X=\{0,\dots,x\}$ and $Y=\{0,\dots,y\}$, answer sets $A=\{0,\dots,a\}$ and $B=\{0,\dots,b\}$, a probability distribution $\pi$ on $X\times Y$ and an acceptance predicate $V_G:X\times Y\times A\times B\to\{0,1\}$. Its entangled value $\omega^*(G)$ is the supremum, over all finite-dimensional entangled strategies (a unit vector $\phi\in\mathbb{C}^{d_A}\otimes\mathbb{C}^{d_B}$ together with POVMs $\{P^x_a\}_{a\in A}$ for each $x\in X$ and $\{Q^y_b\}_{b\in B}$ for each $y\in Y$), of the winning probability $\sum_{x,y}\pi(x,y)\sum_{a,b}V_G(x,y,a,b)\,\langle\phi,(P^x_a\otimes Q^y_b)\phi\rangle$.
--
--   Let $I$ be a finite nonempty set of coordinates and let $m,n$ be finite nonempty index sets. A *repeated model* $M$ over $I$ consists of a probability law $\mu$ on $X\times Y$, a matrix $C\in\mathbb{C}^{m\times n}$ with $\sum_{j,k}|C_{jk}|^2=1$ (equivalently, a unit vector $\psi_C=\sum_{j,k}C_{jk}\,e_j\otimes e_k\in\mathbb{C}^m\otimes\mathbb{C}^n$), for every vector of Alice questions $\vec x\in X^I$ a POVM $\{P_{\vec x}(\alpha)\}_{\alpha\in A^I}$ on $\mathbb{C}^m$, for every vector of Bob questions $\vec y\in Y^I$ a POVM $\{Q_{\vec y}(\beta)\}_{\beta\in B^I}$ on $\mathbb{C}^n$, and a predicate $V:X\times Y\times A\times B\to\{0,1\}$. We assume $\mu=\pi$ and $V=V_G$. The joint law of $M$ on question profiles $z=(x_i,y_i)_{i\in I}$ and answer vectors $(\alpha,\beta)\in A^I\times B^I$ is
--
--   $$
--   \Pr[z,\alpha,\beta]=\prod_{i\in I}\mu(x_i,y_i)\cdot\operatorname{Re}\bigl\langle\psi_C,\bigl(P_{\vec x}(\alpha)\otimes Q_{\vec y}(\beta)\bigr)\psi_C\bigr\rangle ,
--   $$
--
--   where $\vec x=(x_i)_{i\in I}$ and $\vec y=(y_i)_{i\in I}$. Coordinate $i$ is *won* if $V(x_i,y_i,\alpha_i,\beta_i)=1$. For an outcome $t=(z,\alpha,\beta)$ let
--
--   $$
--   \mathrm{rate}(t)=\frac1{|I|}\,\#\{i\in I:\ V(x_i,y_i,\alpha_i,\beta_i)=1\}
--   $$
--
--   be the fraction of coordinates won. Then
--
--   $$
--   \mathbb{E}_{t\sim\Pr}\bigl[\mathrm{rate}(t)\bigr]\le\omega^*(G).
--   $$
--
--   In words, in the parallel repetition of $G$ over the coordinates $I$, no finite-dimensional entangled strategy wins more than an $\omega^*(G)$ fraction of the coordinates on average. This first-moment bound is the input for the regime of few repetitions in the threshold parallel-repetition theorem, where Markov's inequality turns it into an $e^{-\delta}$ bound on the probability of winning at least an $\omega^*(G)+\delta$ fraction of the coordinates.
--
--   **Formalization Note** $M$ is a `RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) I m n` with hypotheses `M.μ = G.questionLaw` and `M.V = G.accepts`, and the left-hand side is `M.joint.avg (Tests.rate M.winsAt)`, where the rate is the uniform average over $I$ of the indicator that a coordinate is won.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/ConditionedStep.lean#L83-L95

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

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.RepeatedModel
universe u_I
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling FiniteProbability Law MixedExposure
variable {I m n : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (M : RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) I m n)
  (hμ : M.μ = G.questionLaw) (hV : M.V = G.accepts)
include hμ hV

theorem OAI.ThresholdParallelRepetition.RepeatedModel.unconditional_rate_le_value : M.joint.avg (Tests.rate M.winsAt) ≤ entangledValue G := by sorry
