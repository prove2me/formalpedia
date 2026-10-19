-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_step_left
-- name    : OAI.ThresholdParallelRepetition.MixedExposure.step_left
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:05:14.738762+00:00
-- url     : https://prove2.me/theorems/4852f278-cc7e-4531-8cb6-de3f0fb62677
-- title:
--   One-coordinate exposure step on Alice's side: purification movement bounded by an operator-entropy change
-- statement:
--   **Resampling.** Let $X,Y,I$ be finite sets, $\mu$ a probability distribution on $X\times Y$, and $\rho=\mu^{\otimes I}$ the product distribution on profiles $z=(z_j)_{j\in I}$ with $z_j=(x_j,y_j)\in X\times Y$. Fix defaults $x_0\in X$, $y_0\in Y$ and a coordinate $i\in I$. Let $\mu(\cdot\mid y)$ be the conditional law on $X$ given the second component $y$, and $\mu(\cdot\mid x)$ the conditional law on $Y$ given the first component $x$; when the conditioning value has probability $0$ they are replaced by the point mass at $x_0$, respectively $y_0$. For a function $f$ on profiles with values in a real vector space put
--   $$(\mathcal L_if)(z)=\sum_{x\in X}\mu(x\mid y_i)\,f\bigl(z^{x_i\leftarrow x}\bigr),\qquad(\mathcal R_if)(z)=\sum_{y\in Y}\mu(y\mid x_i)\,f\bigl(z^{y_i\leftarrow y}\bigr),$$
--   where $z^{x_i\leftarrow x}$ (resp. $z^{y_i\leftarrow y}$) replaces only the first (resp. second) component of $z_i$. Say that $f$ ignores $x_i$ if $f(z^{x_i\leftarrow x})=f(z)$ for all $z$ and $x$, and that $f$ ignores $y_i$ if $f(z^{y_i\leftarrow y})=f(z)$ for all $z$ and $y$.
--
--   **Matrices.** Let $m,n$ be finite index sets. For $C\in\mathbb{C}^{m\times n}$, $S\in\mathbb{C}^{m\times m}$ and $T\in\mathbb{C}^{n\times n}$ let $\langle S\otimes T\rangle_C=\operatorname{Re}\operatorname{tr}(C^*SCT^{\mathsf T})$, the quadratic form of $S\otimes T$ at the vector $\operatorname{vec}C=\sum_{i,j}C_{ij}e_i\otimes e_j$, and let $\|M\|_2$ denote the Hilbert–Schmidt norm. For a Hermitian matrix $S=\sum_k\lambda_kv_kv_k^*$ let $\Lambda(S)=\sum_k\lambda_k\log\lambda_k\,v_kv_k^*$ (functional calculus, with $\log0=0$).
--
--   **Common purifications.** Let $J$ be a nonempty finite set and $(A_j)_{j\in J}$ positive semidefinite $m\times m$ matrices. Let $\Gamma^A$ be the positive semidefinite matrix indexed by $J\times m$ with blocks
--   $$\Gamma^A_{jk}=\int_0^\infty\bigl(A_j(A_j+sI)^{-1}\bigr)^*\,A_k(A_k+sI)^{-1}\,ds ,$$
--   and let $V^A_j\in\mathbb{C}^{(J\times m)\times m}$ be the block column of $(\Gamma^A)^{1/2}$ with index $j$, so that $(V^A_j)^*V^A_k=\Gamma^A_{jk}$ and $(V^A_j)^*V^A_j=A_j$. For a matrix $T$ belonging to the family put $W^A(T)=V^A_{j(T)}$, where $j(T)$ is a fixed index with $A_{j(T)}=T$. For a second nonempty finite set $K$ and positive semidefinite $n\times n$ matrices $(B_k)_{k\in K}$ define $W^B$ in the same way.
--
--   **Theorem.** Assume $0\le A_j\le I$ for all $j\in J$ and $B_k\ge0$ for all $k\in K$, and let $C\in\mathbb{C}^{m\times n}$. Let $F$ assign to every profile a matrix of the family $(A_j)$ and $H$ assign to every profile a matrix of the family $(B_k)$, and assume that $T:=\mathcal L_iF$ also takes all its values in the family $(A_j)$. Assume that $F$ ignores $y_i$ and $H$ ignores $x_i$, and let $\theta\ge0$ be a real function on profiles that ignores both $x_i$ and $y_i$. Then, with all functions evaluated at $z\sim\rho$,
--
--   $$
--   \mathbb{E}_\rho\Bigl[\theta\,\bigl\|\bigl(W^A(F)-W^A(T)\bigr)\,C\,W^B(H)^{\mathsf T}\bigr\|_2^2\Bigr]\;\le\;\mathbb{E}_\rho\bigl[\theta\,\langle\Lambda(F)\otimes\mathcal R_iH\rangle_C\bigr]-\mathbb{E}_\rho\bigl[\theta\,\langle\Lambda(T)\otimes H\rangle_C\bigr].
--   $$
--
--   This is Alice's half of a single step of an exposure chain in which the players' operators are refined one coordinate at a time. The left side measures how far Alice's common purification moves when her operator $F$ is replaced by its conditional average $T=\mathcal L_iF$ over the $i$-th first component, as seen through Bob's purification of $H$; the right side is the corresponding change of the operator-entropy potential $\mathbb{E}_\rho[\theta\langle\Lambda(\cdot)\otimes\cdot\rangle_C]$, written so that it telescopes along a chain in which $T,H$ are the operators at one stage and $F,\mathcal R_iH$ those at the next.
--
--   **Formalization Note** $W^A(T)$ is `commonMap A T = finitePurification A (effectIndex A T)`, $\Lambda$ is `effectEntropy` (`cfc` of $t\mapsto t\log t$), $\langle S\otimes T\rangle_C$ is `prob C S T`, $\mathcal L_i$ and $\mathcal R_i$ are `μ.left x₀ i` and `μ.right y₀ i`, the ignoring conditions are `IgnoresRight F i`, `IgnoresLeft H i`, `IgnoresLeft θ i`, `IgnoresRight θ i`, and the range conditions are `F z ∈ Set.range A`, `μ.left x₀ i F z ∈ Set.range A`, `H z ∈ Set.range B`. The integral defining $\Gamma^A$ is a Bochner integral over $(0,\infty)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/MixedExposure.lean#L17-L75

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

open OAI OAI.ThresholdParallelRepetition
universe u_X u_Y u_I u_m u_n u_J u_K
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {m : Type u_m} {n : Type u_n} {J : Type u_J} {K : Type u_K} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype J] [DecidableEq J] [Nonempty J] [Fintype K] [DecidableEq K] [Nonempty K]

theorem OAI.ThresholdParallelRepetition.MixedExposure.step_left (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (i : I)
    (C : Matrix m n ℂ) (A : J → Matrix m m ℂ) (B : K → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1) (hB : ∀ j, (B j).PosSemidef)
    (F : Profile I X Y → Matrix m m ℂ) (H : Profile I X Y → Matrix n n ℂ)
    (hF : ∀ z, F z ∈ Set.range A) (hF0 : ∀ z, μ.left x₀ i F z ∈ Set.range A)
    (hH : ∀ z, H z ∈ Set.range B) (hFi : IgnoresRight F i) (hHi : IgnoresLeft H i)
    (θ : Profile I X Y → ℝ) (hθ : ∀ z, 0 ≤ θ z)
    (hθL : IgnoresLeft θ i) (hθR : IgnoresRight θ i) :
    (pi (fun _ : I => μ)).avg (fun z => θ z * hsSq
      ((commonMap A (F z) - commonMap A (μ.left x₀ i F z))*C*(commonMap B (H z))ᵀ)) ≤
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (effectEntropy (F z)) (μ.right y₀ i H z)) -
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (effectEntropy (μ.left x₀ i F z)) (H z)) := by sorry
