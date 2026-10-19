-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_RepeatedModel_good_event_step
-- name    : OAI.ThresholdParallelRepetition.RepeatedModel.good_event_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:26:04.314322+00:00
-- url     : https://prove2.me/theorems/6a2c5f4a-f5dd-45a1-86c2-eca84f6bdbc9
-- title:
--   Given that all coordinates of $K$ are won, a random coordinate is also won with probability at most $\omega^*(G)+\delta/2$
-- statement:
--   Let $G$ be a two-player nonlocal game with question sets $X=\{0,\dots,x\}$ and $Y=\{0,\dots,y\}$, answer sets $A=\{0,\dots,a\}$ and $B=\{0,\dots,b\}$, a probability distribution $\pi$ on $X\times Y$ and an acceptance predicate $V_G:X\times Y\times A\times B\to\{0,1\}$. Its entangled value $\omega^*(G)$ is the supremum, over all finite-dimensional entangled strategies (a unit vector $\phi\in\mathbb{C}^{d_A}\otimes\mathbb{C}^{d_B}$ together with POVMs $\{P^x_a\}_{a\in A}$ for each $x\in X$ and $\{Q^y_b\}_{b\in B}$ for each $y\in Y$), of the winning probability $\sum_{x,y}\pi(x,y)\sum_{a,b}V_G(x,y,a,b)\,\langle\phi,(P^x_a\otimes Q^y_b)\phi\rangle$.
--
--   Let $I$ be a finite nonempty set of coordinates and let $m,n$ be finite nonempty index sets. A *repeated model* $M$ over $I$ consists of a probability law $\mu$ on $X\times Y$, a matrix $C\in\mathbb{C}^{m\times n}$ with $\sum_{j,k}|C_{jk}|^2=1$ (equivalently, a unit vector $\psi_C=\sum_{j,k}C_{jk}\,e_j\otimes e_k\in\mathbb{C}^m\otimes\mathbb{C}^n$), for every vector of Alice questions $\vec x\in X^I$ a POVM $\{P_{\vec x}(\alpha)\}_{\alpha\in A^I}$ on $\mathbb{C}^m$, for every vector of Bob questions $\vec y\in Y^I$ a POVM $\{Q_{\vec y}(\beta)\}_{\beta\in B^I}$ on $\mathbb{C}^n$, and a predicate $V:X\times Y\times A\times B\to\{0,1\}$. We assume $\mu=\pi$ and $V=V_G$. The joint law of $M$ on question profiles $z=(x_i,y_i)_{i\in I}$ and answer vectors $(\alpha,\beta)\in A^I\times B^I$ is
--
--   $$
--   \Pr[z,\alpha,\beta]=\prod_{i\in I}\mu(x_i,y_i)\cdot\operatorname{Re}\bigl\langle\psi_C,\bigl(P_{\vec x}(\alpha)\otimes Q_{\vec y}(\beta)\bigr)\psi_C\bigr\rangle ,
--   $$
--
--   where $\vec x=(x_i)_{i\in I}$ and $\vec y=(y_i)_{i\in I}$. Coordinate $i$ is *won* if $V(x_i,y_i,\alpha_i,\beta_i)=1$. For $K\subseteq I$ the mass $\mathfrak{m}(K)$ is the probability, under the joint law, that every coordinate in $K$ is won.
--
--   **Theorem.** Let $K\subseteq I$ and $0<\delta\le1$, and assume $\mathfrak{m}(K)>0$, $|K|<|I|$, $|K|\le\delta|I|/4$ and
--
--   $$
--   \frac{\log\bigl(((a+1)(b+1))^{|K|}/\mathfrak{m}(K)\bigr)}{|I|-|K|}\le\frac{\delta^8}{2^{80}}
--   $$
--
--   (natural logarithm). Then
--
--   $$
--   \frac1{|I|}\sum_{i\in I}\mathfrak{m}(K\cup\{i\})\le\Bigl(\omega^*(G)+\frac{\delta}{2}\Bigr)\,\mathfrak{m}(K).
--   $$
--
--   Equivalently: conditioned on winning all coordinates of $K$, a uniformly random coordinate of $I$ is also won with probability at most $\omega^*(G)+\delta/2$, provided $K$ is a small fraction of the coordinates and the conditioning event is not too unlikely relative to the number $((a+1)(b+1))^{|K|}$ of answer patterns on $K$. Iterating this step bounds the probability of winning many coordinates of a parallel-repeated game.
--
--   **Formalization Note** $M$ is a `RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) I m n` with hypotheses `M.μ = G.questionLaw` and `M.V = G.accepts`; $\mathfrak{m}(K)$ is `M.mass c` and the left-hand side is `(uniform (R := I)).avg (fun i => M.mass (insert i c))`. The denominator $|I|-|K|$ is a natural-number subtraction cast to a real number, which equals the true difference because $|K|<|I|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/ConditionedStep.lean#L50-L69

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

theorem OAI.ThresholdParallelRepetition.RepeatedModel.good_event_step (c : Finset I) (hp : 0 < M.mass c) (hc : c.card < Fintype.card I)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsize : (c.card : ℝ) ≤ δ*(Fintype.card I : ℝ)/4)
    (hsmall : Real.log ((((a+1)*(b+1) : ℕ) : ℝ)^c.card/M.mass c) /
      ((Fintype.card I-c.card : ℕ) : ℝ) ≤ δ^8/(2:ℝ)^80) :
    (uniform (R := I)).avg (fun i => M.mass (insert i c)) ≤ (entangledValue G+δ/2)*M.mass c := by sorry
