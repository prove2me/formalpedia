-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_chain_error_bounds
-- name    : OAI.ThresholdParallelRepetition.MixedExposure.chain_error_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:06:24.62143+00:00
-- url     : https://prove2.me/theorems/125f8d3b-0ee5-4cc7-be2f-512625eebaed
-- title:
--   Telescoping entropy bound for purification errors along a hybrid resampling chain
-- statement:
--   Let $X$, $Y$, $I$ and $R$ be finite sets with $R$ nonempty, and let $m$, $n$ be finite index sets. A *profile* is a family $z=(z_i)_{i\in I}$ of question pairs $z_i=(x_i,y_i)\in X\times Y$, and for $i\in I$ and $q\in X\times Y$ we write $z^{i\leftarrow q}$ for the profile obtained from $z$ by replacing $z_i$ with $q$. Let $\mu$ be a probability distribution on $X\times Y$ and write $\mathbb{E}_z$ for the expectation over $z\sim\mu^{\otimes I}$, the product distribution under which the coordinates $z_i$ are independent with law $\mu$. Fix $x_0\in X$ and $y_0\in Y$. For $x\in X$ let $\mu(\cdot\mid x)$ be the conditional law of the second component given that the first equals $x$, and for $y\in Y$ let $\mu(\cdot\mid y)$ be the conditional law of the first component given that the second equals $y$; when the conditioning value has probability $0$, these are the point masses at $y_0$ and at $x_0$, respectively. For a function $f$ of profiles with values in a real vector space and a coordinate $i\in I$, the resampling operators are
--   $$(L_if)(z)=\mathbb{E}_{x'\sim\mu(\cdot\mid y_i)}\,f(z\text{ with }x_i\text{ replaced by }x'),\qquad(R_if)(z)=\mathbb{E}_{y'\sim\mu(\cdot\mid x_i)}\,f(z\text{ with }y_i\text{ replaced by }y').$$
--   A function of profiles *ignores* $x_i$ (resp. $y_i$) if its value does not change when only Alice's question $x_i$ (resp. only Bob's question $y_i$) at coordinate $i$ is changed.
--
--   For $C\in\mathbb{C}^{m\times n}$, $A\in\mathbb{C}^{m\times m}$ and $B\in\mathbb{C}^{n\times n}$ put $\langle A\otimes B\rangle_C=\operatorname{Re}\operatorname{tr}(C^*ACB^{\mathsf T})$; this is $\operatorname{Re}\langle\psi_C,(A\otimes B)\psi_C\rangle$ for the vector $\psi_C=\sum_{a,b}C_{ab}\,e_a\otimes e_b$ of $\mathbb{C}^m\otimes\mathbb{C}^n$. Let $\|M\|_F^2=\sum_{a,b}|M_{ab}|^2$ be the squared Frobenius (Hilbert–Schmidt) norm. For a finite family $\mathcal A=(A_t)_{t\in J}$ of positive semidefinite $m\times m$ matrices, the *common purification* is defined as follows: let $G$ be the positive semidefinite $(J\times m)\times(J\times m)$ matrix with blocks $G_{tu}=\int_0^\infty K_s(A_t)^*K_s(A_u)\,ds$, where $K_s(A)=A(A+sI)^{-1}$, and let $W_t\in\mathbb{C}^{(J\times m)\times m}$ consist of the columns of $G^{1/2}$ indexed by $\{t\}\times m$, so that $W_t^*W_t=A_t$. For a matrix $T$ put $W^{\mathcal A}(T)=W_t$, where $t$ is a fixed choice of index with $A_t=T$ (a fixed arbitrary index if $T$ is not a member of the family). Families of $n\times n$ matrices are treated in the same way.
--
--   Now let $l=(l_0,\dots,l_{k-1})$ be a list of pairwise distinct coordinates in $I$ and let $C\in\mathbb{C}^{m\times n}$ satisfy $\|C\|_F^2\le1$. For $r\in R$ let $F_r$ and $H_r$ map profiles to complex $m\times m$ and $n\times n$ matrices with $0\le F_r(z)\le I$ and $0\le H_r(z)\le I$ in the Loewner order for every $z$, such that each $F_r$ ignores all of Bob's questions $y_i$ ($i\in I$) and each $H_r$ ignores all of Alice's questions $x_i$ ($i\in I$). Let $\theta_r$ be real functions of profiles with $0\le\theta_r\le1$ that ignore both $x_i$ and $y_i$ for every coordinate $i$ occurring in $l$, and let $p>0$ satisfy
--   $$\sum_{r\in R}\mathbb{E}_z\,\theta_r(z)\,\langle F_r(z)\otimes H_r(z)\rangle_C=p .$$
--   For $0\le j\le k$ define the hybrid chain
--   $$f^r_j=L_{l_j}L_{l_{j+1}}\cdots L_{l_{k-1}}F_r,\qquad h^r_j=R_{l_{j-1}}\cdots R_{l_1}R_{l_0}H_r,$$
--   in which Alice's questions at $l_j,\dots,l_{k-1}$ and Bob's questions at $l_0,\dots,l_{j-1}$ are resampled (so $f^r_k=F_r$ and $h^r_0=H_r$). Let $\mathcal A=(f^r_j(z))_{(j,r,z)}$ and $\mathcal B=(h^r_j(z))_{(j,r,z)}$ be the families indexed by $J=\{0,\dots,k\}\times R\times(X\times Y)^I$, and write $U^r_j(z)=W^{\mathcal A}(f^r_j(z))$ and $V^r_j(z)=W^{\mathcal B}(h^r_j(z))$. Then both of the following hold.
--
--   1. (Alice's steps)
--   $$\sum_{j=0}^{k-1}\sum_{r\in R}\mathbb{E}_z\,\theta_r(z)\,\Bigl\|\bigl(U^r_{j+1}(z)-U^r_j(z)\bigr)\,C\,V^r_j(z)^{\mathsf T}\Bigr\|_F^2\;\le\;p\log\frac{|R|}{p}.$$
--
--   2. (Bob's steps)
--   $$\sum_{j=0}^{k-1}\sum_{r\in R}\mathbb{E}_z\,\theta_r(z)\,\Bigl\|U^r_{j+1}(z)\,C\,\bigl(V^r_j(z)-V^r_{j+1}(z)\bigr)^{\mathsf T}\Bigr\|_F^2\;\le\;p\log\frac{|R|}{p}.$$
--
--   Since $\|KCL^{\mathsf T}\|_F=\|(K\otimes L)\psi_C\|$, each summand measures how far the jointly purified state moves when one more of Alice's (respectively Bob's) questions is resampled along the chain. The theorem bounds the total movement over all $k$ steps by $p\log(|R|/p)$, independently of $k$; dividing by $k$, an average step costs at most $p\log(|R|/p)/k$. In the parallel-repetition argument, $R$ indexes answer records on a set of already-conditioned coordinates, $\theta_r$ is the indicator that a record wins there, $p$ is the probability of that event, and $l$ lists the remaining coordinates.
--
--   **Formalization Note** The index $j$ ranges over `Fin l.length` and $j+1$ is computed in $\mathbb{N}$, so it denotes the next element of the chain (no wrap-around). Distributions are the finite `Law` structures, $\mathbb{E}_z$ is `(pi (fun _ => μ)).avg`, the conditional laws are `givenFirst`/`givenSecond`, $L_i$ and $R_i$ are `μ.left x₀ i` and `μ.right y₀ i`, the chains are `chainLeft`/`chainRight`, $\langle A\otimes B\rangle_C$ is `prob C A B`, $\|\cdot\|_F^2$ is `hsSq`, and $W^{\mathcal A}$, $W^{\mathcal B}$ are `commonMap` applied to `chainLeftFamily`/`chainRightFamily`. `Real.log` is the natural logarithm. The statement also carries the (here automatic) assumptions that $X$ and $Y$ are nonempty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/ExposureChain.lean#L190-L279

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
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

theorem OAI.ThresholdParallelRepetition.MixedExposure.chain_error_bounds (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l : List I) (hN : l.Nodup)
    (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (hF : ∀ r z, (F r z).PosSemidef) (hF1 : ∀ r z, F r z ≤ 1)
    (hH : ∀ r z, (H r z).PosSemidef) (hH1 : ∀ r z, H r z ≤ 1)
    (hFlocal : ∀ r i, IgnoresRight (F r) i) (hHlocal : ∀ r i, IgnoresLeft (H r) i)
    (θ : R → Profile I X Y → ℝ) (hθ : ∀ r z, 0 ≤ θ r z) (hθ1 : ∀ r z, θ r z ≤ 1)
    (hθL : ∀ r i, i ∈ l → IgnoresLeft (θ r) i) (hθR : ∀ r i, i ∈ l → IgnoresRight (θ r) i)
    {p : ℝ} (hp : 0 < p)
    (hm : (∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * prob C (F r z) (H r z))) = p) :
    let A := chainLeftFamily μ x₀ l F
    let B := chainRightFamily μ y₀ l H
    (∑ j : Fin l.length, ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * hsSq
      ((commonMap A (chainLeft μ x₀ l F (j+1) r z)-commonMap A (chainLeft μ x₀ l F j r z))*C*
        (commonMap B (chainRight μ y₀ l H j r z))ᵀ))) ≤ p*Real.log ((Fintype.card R : ℝ)/p) ∧
    (∑ j : Fin l.length, ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * hsSq
      (commonMap A (chainLeft μ x₀ l F (j+1) r z)*C*
        (commonMap B (chainRight μ y₀ l H j r z)-commonMap B (chainRight μ y₀ l H (j+1) r z))ᵀ))) ≤
      p*Real.log ((Fintype.card R : ℝ)/p) := by sorry
