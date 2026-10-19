-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_massAt_left
-- name    : OAI.ThresholdParallelRepetition.MixedExposure.massAt_left
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:12:12.962582+00:00
-- url     : https://prove2.me/theorems/1a467b3d-5890-4243-8154-49e1c666ca9d
-- title:
--   Resampling Alice's question at a pinned coordinate averages the coordinate mass
-- statement:
--   Let $X$, $Y$, $I$, $R$ be finite sets and $m$, $n$ finite index sets. A *profile* is a family $z=(z_i)_{i\in I}$ of question pairs $z_i=(x_i,y_i)\in X\times Y$, and for $i\in I$ and $q\in X\times Y$ we write $z^{i\leftarrow q}$ for the profile obtained from $z$ by replacing $z_i$ with $q$. Let $\mu$ be a probability distribution on $X\times Y$ and write $\mathbb{E}_z$ for the expectation over $z\sim\mu^{\otimes I}$, the product distribution under which the coordinates $z_i$ are independent with law $\mu$. Fix $x_0\in X$, and for $y\in Y$ let $\mu(\cdot\mid y)$ be the conditional law of the first component given that the second equals $y$ (the point mass at $x_0$ if $y$ has probability $0$). For $C\in\mathbb{C}^{m\times n}$, $A\in\mathbb{C}^{m\times m}$ and $B\in\mathbb{C}^{n\times n}$ put $\langle A\otimes B\rangle_C=\operatorname{Re}\operatorname{tr}(C^*ACB^{\mathsf T})$; this is $\operatorname{Re}\langle\psi_C,(A\otimes B)\psi_C\rangle$ for the vector $\psi_C=\sum_{a,b}C_{ab}\,e_a\otimes e_b$ of $\mathbb{C}^m\otimes\mathbb{C}^n$.
--
--   Let $\theta_r$ ($r\in R$) be real functions of profiles, $p$ a real number, $i\in I$ a coordinate, $C\in\mathbb{C}^{m\times n}$, and let $F_r$, $H_r$ ($r\in R$) map profiles to complex $m\times m$ and $n\times n$ matrices. The *mass at coordinate $i$* of a question pair $q$ is
--   $$\mathfrak m_i(F,H)(q)=\frac1p\sum_{r\in R}\mathbb{E}_z\,\theta_r(z)\,\bigl\langle F_r(z^{i\leftarrow q})\otimes H_r(z^{i\leftarrow q})\bigr\rangle_C .$$
--   Alice's resampling operator at $i$ is $(L_iF_r)(z)=\mathbb{E}_{x'\sim\mu(\cdot\mid y_i)}F_r(z\text{ with }x_i\text{ replaced by }x')$, and $LF$ denotes the family $(L_iF_r)_{r\in R}$. Suppose that every $H_r$ ignores Alice's question at $i$, that is, $H_r(z)$ does not change when only $x_i$ is changed. Then for every $q=(x,y)\in X\times Y$,
--
--   $$
--   \mathfrak m_i(LF,H)(x,y)=\mathbb{E}_{x'\sim\mu(\cdot\mid y)}\,\mathfrak m_i(F,H)(x',y) .
--   $$
--
--   In particular the left-hand side does not depend on $x$. Pinning coordinate $i$ to $(x,y)$ and then resampling Alice's question there is the same as averaging the pinned mass over Alice's question drawn from its conditional law given $y$. No positivity or normalization assumptions on $\theta$, $p$, $C$, $F$ or $H$ are needed. This is the mirror image of the corresponding identity for Bob's resampling, and is used to compute the squared norm of a state built from Alice's resampled effects as a conditional average of coordinate masses.
--
--   **Formalization Note** `massAt μ θ p i C F H q` is $\mathfrak m_i(F,H)(q)$; it uses Lean's convention $1/0=0$, so for $p=0$ both sides vanish. $L_iF_r$ is `μ.left x₀ i (F r)`, $\mu(\cdot\mid y)$ is `μ.givenSecond x₀ y`, $z^{i\leftarrow q}$ is `Function.update z i q`, $\langle A\otimes B\rangle_C$ is `prob C A B`, and the hypothesis is `IgnoresLeft (H r) i` for all $r$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/ExposureChain.lean#L339-L364

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

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MixedExposure
universe u_I u_X u_Y u_R u_m u_n u_E u_Z
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq X] [DecidableEq Y]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq Y] [DecidableEq m] [DecidableEq n] in
theorem OAI.ThresholdParallelRepetition.MixedExposure.massAt_left (μ : Law (X×Y)) (x₀ : X) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ) (hH : ∀ r, IgnoresLeft (H r) i) (q : X×Y) :
    massAt μ θ p i C (fun r => μ.left x₀ i (F r)) H q =
      (μ.givenSecond x₀ q.2).avg (fun x => massAt μ θ p i C F H (x,q.2)) := by sorry
