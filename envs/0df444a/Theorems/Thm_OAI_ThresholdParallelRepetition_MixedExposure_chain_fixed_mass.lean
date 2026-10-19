-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_chain_fixed_mass
-- name    : OAI.ThresholdParallelRepetition.MixedExposure.chain_fixed_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:16:32.033292+00:00
-- url     : https://prove2.me/theorems/917eb219-fa2b-49fa-a7cf-1dbb4c61665b
-- title:
--   Resamplings at other coordinates preserve the mass at a pinned fresh coordinate
-- statement:
--   Let $X$, $Y$, $I$, $R$ be finite sets and $m$, $n$ finite index sets. A *profile* is a family $z=(z_i)_{i\in I}$ of question pairs $z_i=(x_i,y_i)\in X\times Y$, and for $i\in I$ and $q\in X\times Y$ we write $z^{i\leftarrow q}$ for the profile obtained from $z$ by replacing $z_i$ with $q$. Let $\mu$ be a probability distribution on $X\times Y$ and write $\mathbb{E}_z$ for the expectation over $z\sim\mu^{\otimes I}$, the product distribution under which the coordinates $z_i$ are independent with law $\mu$. Fix $x_0\in X$ and $y_0\in Y$. For $x\in X$ let $\mu(\cdot\mid x)$ be the conditional law of the second component given that the first equals $x$, and for $y\in Y$ let $\mu(\cdot\mid y)$ be the conditional law of the first component given that the second equals $y$; when the conditioning value has probability $0$, these are the point masses at $y_0$ and at $x_0$, respectively. For a function $f$ of profiles with values in a real vector space and a coordinate $i\in I$, the resampling operators are
--   $$(L_if)(z)=\mathbb{E}_{x'\sim\mu(\cdot\mid y_i)}\,f(z\text{ with }x_i\text{ replaced by }x'),\qquad(R_if)(z)=\mathbb{E}_{y'\sim\mu(\cdot\mid x_i)}\,f(z\text{ with }y_i\text{ replaced by }y').$$
--   A function of profiles *ignores* $x_i$ (resp. $y_i$) if its value does not change when only Alice's question $x_i$ (resp. only Bob's question $y_i$) at coordinate $i$ is changed. For $C\in\mathbb{C}^{m\times n}$, $A\in\mathbb{C}^{m\times m}$ and $B\in\mathbb{C}^{n\times n}$ put $\langle A\otimes B\rangle_C=\operatorname{Re}\operatorname{tr}(C^*ACB^{\mathsf T})$; this is $\operatorname{Re}\langle\psi_C,(A\otimes B)\psi_C\rangle$ for the vector $\psi_C=\sum_{a,b}C_{ab}\,e_a\otimes e_b$ of $\mathbb{C}^m\otimes\mathbb{C}^n$.
--
--   For real functions $\theta_r$ ($r\in R$) of profiles, a real number $p$, a matrix $C\in\mathbb{C}^{m\times n}$ and functions $F_r$, $H_r$ from profiles to complex $m\times m$ and $n\times n$ matrices, the *mass at coordinate $i$* of a question pair $q$ is
--   $$\mathfrak m_i(F,H)(q)=\frac1p\sum_{r\in R}\mathbb{E}_z\,\theta_r(z)\,\bigl\langle F_r(z^{i\leftarrow q})\otimes H_r(z^{i\leftarrow q})\bigr\rangle_C .$$
--
--   Let $l=(l_0,\dots,l_{k-1})$ be a list of pairwise distinct coordinates in $I$. Assume that every $F_r$ ignores all of Bob's questions $y_i$ ($i\in I$), every $H_r$ ignores all of Alice's questions $x_i$ ($i\in I$), and every $\theta_r$ ignores both $x_i$ and $y_i$ for each coordinate $i$ occurring in $l$; nothing else is assumed about $C$, $p$, $F$, $H$ or $\theta$. For $0\le j<k$ consider the hybrid effects
--   $$f^r_{j+1}=L_{l_{j+1}}\cdots L_{l_{k-1}}F_r,\qquad h^r_j=R_{l_{j-1}}\cdots R_{l_0}H_r$$
--   (so $f^r_k=F_r$ and $h^r_0=H_r$), and write $f_{j+1}=(f^r_{j+1})_r$, $h_j=(h^r_j)_r$. Then for every $q\in X\times Y$,
--
--   $$
--   \mathfrak m_{l_j}(f_{j+1},h_j)(q)=\mathfrak m_{l_j}(F,H)(q).
--   $$
--
--   The coordinate $l_j$ is the one at which the hybrid chain switches from resampling Alice's questions to resampling Bob's questions, and it is touched by neither $f^r_{j+1}$ nor $h^r_j$. The identity says that, with this fresh coordinate pinned to an arbitrary question pair $q$, the resamplings at all other coordinates of $l$ leave the mass unchanged. Combined with the fact that $\theta_r$ does not see coordinate $l_j$, it identifies the squared norm of the intermediate state of the chain at step $j$ with the density of the question pair at coordinate $l_j$.
--
--   **Formalization Note** $f^r_{j+1}$ and $h^r_j$ are `chainLeft μ x₀ l F (j+1) r` and `chainRight μ y₀ l H j r`; $j$ ranges over `Fin l.length` and $j+1$ is computed in $\mathbb{N}$. `massAt` is $\mathfrak m_i$, with Lean's convention $1/0=0$. The hypotheses are `l.Nodup`, `IgnoresRight (F r) i` and `IgnoresLeft (H r) i` for all $r,i$, and `IgnoresLeft (θ r) i`, `IgnoresRight (θ r) i` for $i\in l$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/FreshStates.lean#L144-L171

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

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MixedExposure
universe u_X u_Y u_I u_E u_R u_m u_n u_u u_v u_Z
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
theorem OAI.ThresholdParallelRepetition.MixedExposure.chain_fixed_mass (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l : List I) (hN : l.Nodup)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ)
    (hF : ∀ r i, IgnoresRight (F r) i) (hH : ∀ r i, IgnoresLeft (H r) i)
    (θ : R → Profile I X Y → ℝ)
    (hθL : ∀ r i, i ∈ l → IgnoresLeft (θ r) i) (hθR : ∀ r i, i ∈ l → IgnoresRight (θ r) i)
    (p : ℝ) (j : Fin l.length) (q : X×Y) :
    massAt μ θ p l[j.val] C (chainLeft μ x₀ l F (j+1)) (chainRight μ y₀ l H j) q =
      massAt μ θ p l[j.val] C F H q := by sorry
