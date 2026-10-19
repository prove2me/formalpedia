-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_EventSystem_rawA_norm
-- name    : OAI.ThresholdParallelRepetition.MixedExposure.EventSystem.rawA_norm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:17:54.129321+00:00
-- url     : https://prove2.me/theorems/8517600a-8099-4e6f-a47f-efc6c0b76947
-- title:
--   Squared norm of Alice's raw exposure state is a conditional coordinate density
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
--   For $0\le j<k$ and $x\in X$, *Alice's raw state* is
--   $$\mathrm{raw}^A_j(x)=\mathcal S_{l_j}\bigl(U_{j+1},V_{j+1};(x,y_0)\bigr).$$
--   Finally, the *event density* and its *coordinate densities* are
--   $$\rho(z)=\frac1p\sum_{r\in R}\theta_r(z)\,\langle F_r(z)\otimes H_r(z)\rangle_C,\qquad g_i(q)=\mathbb{E}_z\,\rho(z^{i\leftarrow q})\quad(i\in I,\ q\in X\times Y).$$
--
--   For every $j\in\{0,\dots,k-1\}$ and every $x\in X$,
--
--   $$
--   \bigl\|\mathrm{raw}^A_j(x)\bigr\|_F^2=\mathbb{E}_{y\sim\mu(\cdot\mid x)}\,g_{l_j}(x,y).
--   $$
--
--   Since $\mathbb{E}_z\rho(z)=1$, the function $\rho$ is the density of the conditioned law $\nu=\rho\,\mu^{\otimes I}$, $g_i$ is the density, relative to $\mu$, of the question pair at coordinate $i$ under $\nu$, and for $x$ of positive probability the right-hand side is the density of Alice's question at coordinate $l_j$ relative to the first marginal of $\mu$. The state $\mathrm{raw}^A_j(x)$ depends only on Alice's question $x$ at the fresh coordinate (the pinned value $y_0$ is immaterial, since $U_{j+1}$ and $V_{j+1}$ ignore Bob's question at $l_j$). The identity is used to bound the cost of normalizing it to a unit state: by the formula $\|C-C/\|C\|_F\|_F^2=(\|C\|_F-1)^2$ this cost becomes a Hellinger-type quantity controlled by relative entropy.
--
--   **Formalization Note** `S : EventSystem X Y I R m n` bundles the data above. `S.rawA j x` is `stateAt` at coordinate `S.l[j]` with the purification maps `S.U (j+1)`, `S.V (j+1)` (built by `commonMap` from `chainLeftFamily` and `chainRightFamily`) and the pinned pair `(x, S.y₀)`. `coordDensity (fun _ => S.μ) S.density i q` is $g_i(q)$, `S.μ.givenFirst S.y₀ x` is $\mu(\cdot\mid x)$, and `hsSq` is $\|\cdot\|_F^2$. The index $j$ ranges over `Fin S.l.length` and $j+1$ is computed in $\mathbb{N}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/ExposureData.lean#L111-L123

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

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MixedExposure OAI.ThresholdParallelRepetition.MixedExposure.EventSystem
universe u_X u_Y u_I u_R u_m u_n
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable (X : Type u_X) (Y : Type u_Y) (I : Type u_I) (R : Type u_R) (m : Type u_m) (n : Type u_n) [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [DecidableEq R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {X Y I R m n} [Nonempty X] [Nonempty Y] [Nonempty R]
variable (S : EventSystem X Y I R m n)

theorem OAI.ThresholdParallelRepetition.MixedExposure.EventSystem.rawA_norm (j : Fin S.l.length) (x : X) : hsSq (S.rawA j x) =
    (S.μ.givenFirst S.y₀ x).avg (fun y => coordDensity (fun _ : I => S.μ) S.density S.l[j.val] (x,y)) := by sorry
