-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_massAt_right
-- name    : OAI.ThresholdParallelRepetition.MixedExposure.massAt_right
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:09:18.950714+00:00
-- url     : https://prove2.me/theorems/60b8b04a-c60b-4113-9c7c-0abdcf3bb1ca
-- title:
--   Resampling Bob's question at a pinned coordinate averages the coordinate mass
-- statement:
--   Let $X$, $Y$, $I$, $R$ be finite sets and $m$, $n$ finite index sets. A *profile* is a family $z=(z_i)_{i\in I}$ of question pairs $z_i=(x_i,y_i)\in X\times Y$, and for $i\in I$ and $q\in X\times Y$ we write $z^{i\leftarrow q}$ for the profile obtained from $z$ by replacing $z_i$ with $q$. Let $\mu$ be a probability distribution on $X\times Y$ and write $\mathbb{E}_z$ for the expectation over $z\sim\mu^{\otimes I}$, the product distribution under which the coordinates $z_i$ are independent with law $\mu$. Fix $y_0\in Y$, and for $x\in X$ let $\mu(\cdot\mid x)$ be the conditional law of the second component given that the first equals $x$ (the point mass at $y_0$ if $x$ has probability $0$). For $C\in\mathbb{C}^{m\times n}$, $A\in\mathbb{C}^{m\times m}$ and $B\in\mathbb{C}^{n\times n}$ put $\langle A\otimes B\rangle_C=\operatorname{Re}\operatorname{tr}(C^*ACB^{\mathsf T})$; this is $\operatorname{Re}\langle\psi_C,(A\otimes B)\psi_C\rangle$ for the vector $\psi_C=\sum_{a,b}C_{ab}\,e_a\otimes e_b$ of $\mathbb{C}^m\otimes\mathbb{C}^n$.
--
--   Let $\theta_r$ ($r\in R$) be real functions of profiles, $p$ a real number, $i\in I$ a coordinate, $C\in\mathbb{C}^{m\times n}$, and let $F_r$, $H_r$ ($r\in R$) map profiles to complex $m\times m$ and $n\times n$ matrices. The *mass at coordinate $i$* of a question pair $q$ is
--   $$\mathfrak m_i(F,H)(q)=\frac1p\sum_{r\in R}\mathbb{E}_z\,\theta_r(z)\,\bigl\langle F_r(z^{i\leftarrow q})\otimes H_r(z^{i\leftarrow q})\bigr\rangle_C .$$
--   Bob's resampling operator at $i$ is $(R_iH_r)(z)=\mathbb{E}_{y'\sim\mu(\cdot\mid x_i)}H_r(z\text{ with }y_i\text{ replaced by }y')$, and $RH$ denotes the family $(R_iH_r)_{r\in R}$. Suppose that every $F_r$ ignores Bob's question at $i$, that is, $F_r(z)$ does not change when only $y_i$ is changed. Then for every $q=(x,y)\in X\times Y$,
--
--   $$
--   \mathfrak m_i(F,RH)(x,y)=\mathbb{E}_{y'\sim\mu(\cdot\mid x)}\,\mathfrak m_i(F,H)(x,y') .
--   $$
--
--   In particular the left-hand side does not depend on $y$. Pinning coordinate $i$ to $(x,y)$ and then resampling Bob's question there is the same as averaging the pinned mass over Bob's question drawn from its conditional law given $x$. No positivity or normalization assumptions on $\theta$, $p$, $C$, $F$ or $H$ are needed. The identity is used to compute the squared norm of a state built from Bob's resampled effects as a conditional average of coordinate masses.
--
--   **Formalization Note** `massAt μ θ p i C F H q` is $\mathfrak m_i(F,H)(q)$; it uses Lean's convention $1/0=0$, so for $p=0$ both sides vanish. $R_iH_r$ is `μ.right y₀ i (H r)`, $\mu(\cdot\mid x)$ is `μ.givenFirst y₀ x`, $z^{i\leftarrow q}$ is `Function.update z i q`, $\langle A\otimes B\rangle_C$ is `prob C A B`, and the hypothesis is `IgnoresRight (F r) i` for all $r$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/ExposureChain.lean#L312-L337

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

omit [DecidableEq X] [DecidableEq m] [DecidableEq n] in
theorem OAI.ThresholdParallelRepetition.MixedExposure.massAt_right (μ : Law (X×Y)) (y₀ : Y) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ) (hF : ∀ r, IgnoresRight (F r) i) (q : X×Y) :
    massAt μ θ p i C F (fun r => μ.right y₀ i (H r)) q =
      (μ.givenFirst y₀ q.1).avg (fun y => massAt μ θ p i C F H (q.1,y)) := by sorry
