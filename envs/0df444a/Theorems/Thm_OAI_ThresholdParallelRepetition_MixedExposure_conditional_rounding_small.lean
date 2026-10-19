-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_conditional_rounding_small
-- name    : OAI.ThresholdParallelRepetition.MixedExposure.conditional_rounding_small
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-18T11:20:48.714514+00:00
-- url     : https://prove2.me/theorems/6c0e3686-7a3c-4e63-9f87-e627b44d87fc
-- title:
--   Conditional rounding: fresh coordinates of an exposure system score at most $\omega^*(G)+\delta/4$ on average
-- statement:
--   Let $G$ be a two-player nonlocal game with question sets $X=\{0,\dots,x\}$ and $Y=\{0,\dots,y\}$, answer sets $A=\{0,\dots,a\}$ and $B=\{0,\dots,b\}$, a probability distribution $\pi$ on $X\times Y$ and an acceptance predicate $V_G:X\times Y\times A\times B\to\{0,1\}$. Its entangled value $\omega^*(G)$ is the supremum, over all finite-dimensional entangled strategies (a unit vector $\phi\in\mathbb{C}^{d_A}\otimes\mathbb{C}^{d_B}$ together with POVMs $\{P^x_a\}_{a\in A}$ for each $x\in X$ and $\{Q^y_b\}_{b\in B}$ for each $y\in Y$), of the winning probability $\sum_{x,y}\pi(x,y)\sum_{a,b}V_G(x,y,a,b)\,\langle\phi,(P^x_a\otimes Q^y_b)\phi\rangle$.
--
--   For a matrix $C\in\mathbb{C}^{m\times n}$ write $\psi_C=\sum_{j,k}C_{jk}\,e_j\otimes e_k\in\mathbb{C}^m\otimes\mathbb{C}^n$ and, for operators $P$ on $\mathbb{C}^m$ and $Q$ on $\mathbb{C}^n$, put $\langle P\otimes Q\rangle_C=\operatorname{Re}\langle\psi_C,(P\otimes Q)\psi_C\rangle$. Let $I$ be a finite set of coordinates, $R$ a finite nonempty set of records, and $m,n$ finite nonempty index sets. A question profile is $z=(x_i,y_i)_{i\in I}\in(X\times Y)^I$, and $z\sim\mu^{\otimes I}$ means that the pairs $(x_i,y_i)$ are independent with law $\mu$.
--
--   An *exposure system* $S$ consists of a probability law $\mu$ on $X\times Y$; a list $l=(l_0,\dots,l_{L-1})$ of pairwise distinct coordinates; a matrix $C\in\mathbb{C}^{m\times n}$ with $\sum_{j,k}|C_{jk}|^2=1$; for every record $r\in R$ and profile $z$, operators $0\le F_r(z)\le\mathbf 1$ on $\mathbb{C}^m$ and $0\le H_r(z)\le\mathbf 1$ on $\mathbb{C}^n$, where $F_r(z)$ depends only on Alice's questions $(x_i)_{i\in I}$ and $H_r(z)$ only on Bob's questions $(y_i)_{i\in I}$; and weights $\theta_r(z)\in[0,1]$ that do not depend on the question pair $(x_i,y_i)$ at any coordinate $i$ occurring in $l$. It is required that $\sum_{r\in R}\theta_r(z)\langle F_r(z)\otimes H_r(z)\rangle_C\le1$ for every $z$, and that the event mass
--
--   $$
--   p=\sum_{r\in R}\mathbb{E}_{z\sim\mu^{\otimes I}}\bigl[\theta_r(z)\,\langle F_r(z)\otimes H_r(z)\rangle_C\bigr]
--   $$
--
--   is strictly positive. A *refinement* $T$ of $S$ assigns to every coordinate $i$, record $r$ and profile $z$ positive semidefinite operators $T^{A}_{i,r,z}(a)$ ($a\in A$) on $\mathbb{C}^m$ and $T^{B}_{i,r,z}(b)$ ($b\in B$) on $\mathbb{C}^n$ with $\sum_{a}T^{A}_{i,r,z}(a)=F_r(z)$ and $\sum_{b}T^{B}_{i,r,z}(b)=H_r(z)$, where $T^{A}$ depends only on Alice's questions and $T^{B}$ only on Bob's. The score of a coordinate $i$ is
--
--   $$
--   \operatorname{score}_T(i)=\frac1p\sum_{r\in R}\mathbb{E}_{z\sim\mu^{\otimes I}}\Bigl[\theta_r(z)\sum_{a\in A,\,b\in B}V_G(x_i,y_i,a,b)\,\bigl\langle T^{A}_{i,r,z}(a)\otimes T^{B}_{i,r,z}(b)\bigr\rangle_C\Bigr].
--   $$
--
--   **Theorem.** Suppose $\mu=\pi$, $L\ge1$, $0<\delta\le1$ and $\log(|R|/p)/L\le\delta^8/2^{80}$ (natural logarithm). Then
--
--   $$
--   \frac1L\sum_{j=0}^{L-1}\operatorname{score}_T(l_j)\le\omega^*(G)+\frac{\delta}{4}.
--   $$
--
--   The data $(\theta,F,H)$ describe a conditioning event of probability $p$ in a parallel-repeated game, and $\operatorname{score}_T(i)$ is the probability of winning coordinate $i$ conditioned on that event. The theorem says that if the event is not too unlikely compared with the number of records and the number $L$ of fresh coordinates, then on average over the fresh coordinates the conditional winning probability exceeds the entangled value by at most $\delta/4$. It is applied with the event "all coordinates of a set $K$ are won", with the answers on $K$ as records and with $l$ an enumeration of the coordinates outside $K$.
--
--   **Formalization Note** Here `S : EventSystem (Fin (x+1)) (Fin (y+1)) I R m n` (the structure also stores reference questions $x_0,y_0$, which only enter internal constructions), `T : Refinement S (Fin (a+1)) (Fin (b+1))`, the score is `T.score i G.accepts`, and $\mu=\pi$ is the hypothesis `S.μ = G.questionLaw`. The locality conditions are stated with `IgnoresLeft`/`IgnoresRight`, operator inequalities refer to the Loewner order, $L$ is `S.l.length` and $|R|$ is `Fintype.card R`. Since $p>0$, the logarithm is applied to a positive number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/Rounding.lean#L189-L202

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

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MixedExposure
universe u_R u_m u_n u_A u_B u_T u_U
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling FiniteProbability Law
variable {I R m n : Type} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (S : EventSystem (Fin (x+1)) (Fin (y+1)) I R m n)
  (hμ : S.μ = G.questionLaw)
  (T : Refinement S (Fin (a+1)) (Fin (b+1)))
include hμ

theorem OAI.ThresholdParallelRepetition.MixedExposure.conditional_rounding_small (hl : 0 < S.l.length) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ) ≤ δ^8/(2:ℝ)^80) :
    (1/(S.l.length : ℝ))*∑ j : Fin S.l.length, T.score S.l[j.val] G.accepts ≤ entangledValue G+δ/4 := by sorry
