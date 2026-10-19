-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_EventSystem_normalized_error_bounds
-- name    : OAI.ThresholdParallelRepetition.MixedExposure.EventSystem.normalized_error_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:19:51.482163+00:00
-- url     : https://prove2.me/theorems/400b53fa-7498-48b5-b2a6-fe79e96f2bf0
-- title:
--   Fresh exposure states are close on average to normalized one-sided states
-- statement:
--   Let $X$, $Y$, $I$, $R$ be finite sets, with $X$, $Y$ and $R$ nonempty, and let $m$, $n$ be finite index sets. A *profile* is a family $z=(z_i)_{i\in I}$ of question pairs $z_i=(x_i,y_i)\in X\times Y$, and for $i\in I$ and $q\in X\times Y$ we write $z^{i\leftarrow q}$ for the profile obtained from $z$ by replacing $z_i$ with $q$. A function of profiles *ignores* $x_i$ (resp. $y_i$) if its value does not change when only Alice's question $x_i$ (resp. only Bob's question $y_i$) at coordinate $i$ is changed.
--
--   An *event system* consists of the following data: a probability distribution $\mu$ on $X\times Y$; points $x_0\in X$ and $y_0\in Y$; a list $l=(l_0,\dots,l_{k-1})$ of pairwise distinct coordinates in $I$; a matrix $C\in\mathbb{C}^{m\times n}$ with $\|C\|_F^2=1$, where $\|M\|_F^2=\sum_{a,b}|M_{ab}|^2$ is the squared Frobenius (Hilbert–Schmidt) norm; for each $r\in R$, functions $F_r$ and $H_r$ from profiles to complex $m\times m$ and $n\times n$ matrices with $0\le F_r(z)\le I$ and $0\le H_r(z)\le I$ in the Loewner order, such that $F_r$ ignores every $y_i$ and $H_r$ ignores every $x_i$ ($i\in I$); functions $\theta_r$ from profiles to $[0,1]$ that ignore both $x_i$ and $y_i$ for every coordinate $i$ occurring in $l$; and a number $p>0$ such that
--   $$\sum_{r\in R}\theta_r(z)\,\langle F_r(z)\otimes H_r(z)\rangle_C\le1\ \text{ for every profile }z,\qquad\sum_{r\in R}\mathbb{E}_z\,\theta_r(z)\,\langle F_r(z)\otimes H_r(z)\rangle_C=p ,$$
--   where $\mathbb{E}_z$ is the expectation over $z\sim\mu^{\otimes I}$ (independent coordinates with law $\mu$) and $\langle A\otimes B\rangle_C=\operatorname{Re}\operatorname{tr}(C^*ACB^{\mathsf T})=\operatorname{Re}\langle\psi_C,(A\otimes B)\psi_C\rangle$ with $\psi_C=\sum_{a,b}C_{ab}\,e_a\otimes e_b$.
--
--   From an event system one builds the following objects. For $x\in X$ let $\mu(\cdot\mid x)$ be the conditional law of the second component given that the first equals $x$, and for $y\in Y$ let $\mu(\cdot\mid y)$ be the conditional law of the first component given that the second equals $y$; when the conditioning value has probability $0$, these are the point masses at $y_0$ and at $x_0$, respectively. For a function $f$ of profiles with values in a real vector space and a coordinate $i\in I$, the resampling operators are
--   $$(L_if)(z)=\mathbb{E}_{x'\sim\mu(\cdot\mid y_i)}\,f(z\text{ with }x_i\text{ replaced by }x'),\qquad(R_if)(z)=\mathbb{E}_{y'\sim\mu(\cdot\mid x_i)}\,f(z\text{ with }y_i\text{ replaced by }y').$$
--   For $0\le j\le k$ define the hybrid chain
--   $$f^r_j=L_{l_j}L_{l_{j+1}}\cdots L_{l_{k-1}}F_r,\qquad h^r_j=R_{l_{j-1}}\cdots R_{l_1}R_{l_0}H_r,$$
--   in which Alice's questions at $l_j,\dots,l_{k-1}$ and Bob's questions at $l_0,\dots,l_{j-1}$ are resampled (so $f^r_k=F_r$ and $h^r_0=H_r$).
--
--   Let $J=\{0,1,\dots,k\}\times R\times(X\times Y)^I$ and consider the families $\mathcal A=(f^r_j(z))_{(j,r,z)\in J}$ of $m\times m$ matrices and $\mathcal B=(h^r_j(z))_{(j,r,z)\in J}$ of $n\times n$ matrices. Their *common purifications* are defined as follows: for $\mathcal A$, let $G$ be the positive semidefinite $(J\times m)\times(J\times m)$ matrix with blocks $G_{tu}=\int_0^\infty K_s(A_t)^*K_s(A_u)\,ds$, where $A_t$ is the member of $\mathcal A$ with index $t$ and $K_s(A)=A(A+sI)^{-1}$, and let $W_t\in\mathbb{C}^{(J\times m)\times m}$ consist of the columns of $G^{1/2}$ indexed by $\{t\}\times m$, so that $W_t^*W_t=A_t$; for a matrix $T$ put $W^{\mathcal A}(T)=W_t$ for a fixed choice of index $t$ with $A_t=T$ (a fixed arbitrary index if there is none). The construction for $\mathcal B$ is the same. Set
--   $$U^r_j(z)=W^{\mathcal A}\bigl(f^r_j(z)\bigr)\in\mathbb{C}^{(J\times m)\times m},\qquad V^r_j(z)=W^{\mathcal B}\bigl(h^r_j(z)\bigr)\in\mathbb{C}^{(J\times n)\times n}.$$
--   For a coordinate $i$, a pair $q\in X\times Y$ and two of these purification maps $U=U_a$, $V=V_b$, the *block state* is the block-diagonal matrix
--   $$\mathcal S_i(U,V;q)=\bigoplus_{(r,z)\in R\times(X\times Y)^I}\sqrt{\frac{\mu^{\otimes I}(z)\,\theta_r(z)}{p}}\;U^r(z^{i\leftarrow q})\,C\,V^r(z^{i\leftarrow q})^{\mathsf T},$$
--   where $\mu^{\otimes I}(z)=\prod_{i'\in I}\mu(z_{i'})$; its rows are indexed by $(J\times m)\times(R\times(X\times Y)^I)$ and its columns by $(J\times n)\times(R\times(X\times Y)^I)$.
--
--   For $0\le j<k$, $q\in X\times Y$, $x\in X$ and $y\in Y$ define the *fresh state* and the two *raw states*
--   $$D_j(q)=\mathcal S_{l_j}(U_{j+1},V_j;q),\qquad\mathrm{raw}^A_j(x)=\mathcal S_{l_j}\bigl(U_{j+1},V_{j+1};(x,y_0)\bigr),\qquad\mathrm{raw}^B_j(y)=\mathcal S_{l_j}\bigl(U_j,V_j;(x_0,y)\bigr).$$
--   Let $E$ be any matrix of the same shape with $\|E\|_F=1$, and normalize the raw states with default $E$:
--   $$M_j(x)=\operatorname{unit}\bigl(\mathrm{raw}^A_j(x),E\bigr),\qquad N_j(y)=\operatorname{unit}\bigl(\mathrm{raw}^B_j(y),E\bigr),\qquad\text{where }\operatorname{unit}(T,E)=\begin{cases}T/\|T\|_F,&T\neq0,\\E,&T=0.\end{cases}$$
--   Then, with $\mathbb{E}_{(x,y)\sim\mu}$ the expectation over a single question pair, both of the following hold:
--
--   1. (Alice's side)
--   $$\sum_{j=0}^{k-1}\mathbb{E}_{(x,y)\sim\mu}\,\bigl\|D_j(x,y)-M_j(x)\bigr\|_F^2\le4\log\frac{|R|}{p}.$$
--
--   2. (Bob's side)
--   $$\sum_{j=0}^{k-1}\mathbb{E}_{(x,y)\sim\mu}\,\bigl\|D_j(x,y)-N_j(y)\bigr\|_F^2\le4\log\frac{|R|}{p}.$$
--
--   Here $M_j(x)$ is a unit-norm state that depends only on Alice's question at the fresh coordinate $l_j$, and $N_j(y)$ is one that depends only on Bob's question there. The theorem says that, averaged over the question pair at the fresh coordinate and summed along the chain, the fresh state $D_j(x,y)$ is close to both one-sided states; for a uniformly random step $j$ the expected squared distances are at most $4\log(|R|/p)/k$. In the parallel-repetition argument this is the input to a rounding step that compares the success rate on the coordinates of $l$, conditioned on the event of probability $p$, with the entangled value of a single copy of the game.
--
--   **Formalization Note** `S : EventSystem X Y I R m n` bundles the data above. `S.D j q`, `S.rawA j x` and `S.rawB j y` are `stateAt` at coordinate `S.l[j]`; `S.M j E x` and `S.N j E y` are `unitize (S.rawA j x) E` and `unitize (S.rawB j y) E`, where `unitize T E` is `if hsSq T = 0 then E else (Real.sqrt (hsSq T))⁻¹ • T` and `hsSq` is $\|\cdot\|_F^2$; the hypothesis on $E$ is `hsSq E = 1`. $\mathbb{E}_{(x,y)\sim\mu}$ is `S.μ.avg`, the index $j$ ranges over `Fin S.l.length` with $j+1$ computed in $\mathbb{N}$, and `Real.log` is the natural logarithm.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/ExposureErrors.lean#L119-L142

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

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MixedExposure OAI.ThresholdParallelRepetition.MixedExposure.EventSystem
universe u_I u_Z u_X u_Y u_R u_m u_n
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable (S : EventSystem X Y I R m n)

theorem OAI.ThresholdParallelRepetition.MixedExposure.EventSystem.normalized_error_bounds (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ)
    (hE : hsSq E = 1) :
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.M j E q.1))) ≤ 4*Real.log ((Fintype.card R : ℝ)/S.p) ∧
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.N j E q.2))) ≤ 4*Real.log ((Fintype.card R : ℝ)/S.p) := by sorry
