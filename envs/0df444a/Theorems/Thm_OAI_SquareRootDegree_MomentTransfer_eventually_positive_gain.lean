-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_MomentTransfer_eventually_positive_gain
-- name    : OAI.SquareRootDegree.MomentTransfer.eventually_positive_gain
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:53:39.118753+00:00
-- url     : https://prove2.me/theorems/ae8770c4-3ed4-4f23-a711-1ddab0d0f978
-- title:
--   Convergence to the Gaussian in distribution and in moments eventually makes the leaf–selector gain exceed $\eta$
-- statement:
--   **Fixed grid.** Let $N=2^{1024}$, $R=96$, $\delta=R/N$ and $h=2^{-1536}$, and index the leaves by $i\in\{0,1,\dots,2N\}$. With $\operatorname{clip}(x)=\max(0,\min(1,x))$ and the hats $\operatorname{hat}_i(t)=\operatorname{clip}(t/\delta+N-i+1)-\operatorname{clip}(t/\delta+N-i)$, the grid centres, leaf tests and selector weights are
--   $$c_i=1+\delta(i-N),\qquad \ell_i(t)=\max\Big(0,1-\frac{|t-c_i|}{h}\Big),\qquad s_i(t)=\operatorname{hat}_i(t)+[i=N]\Big(1-\sum_{j=0}^{2N}\operatorname{hat}_j(t)\Big),$$
--   where $[i=N]$ is $1$ if $i=N$ and $0$ otherwise.
--
--   **Moments and gain.** For a probability space $(\Omega,P)$, a real random variable $T$ on it and a family $u=(u_i)$ of test functions, put $M^{u}_k(i)=\int u_i(T)\,T^k\,dP$ for $k=0,1,2$. For two arrays $l=(l_k(i))$ and $m=(m_k(i))$ indexed by $k\in\{0,1,2\}$ and the leaves $i$, set $\bar\mu_i=l_1(i)/l_0(i)$ and $\bar v_i=l_2(i)/l_0(i)-\bar\mu_i^2$, and define the gain
--   $$\mathcal G(l,m)=\Big(\prod_i l_0(i)\Big)\Big(1+\sum_i\bar v_i-\sum_i\frac{m_2(i)+2(1-\bar\mu_i)\,m_1(i)+\big((1-\bar\mu_i)^2+\sum_{j\neq i}\bar v_j\big)\,m_0(i)}{l_0(i)}\Big).$$
--   Let $\eta=\tfrac12\,\mathcal G(L^{\gamma},S^{\gamma})$, where $L^\gamma=M^{\ell}$ and $S^\gamma=M^{s}$ are the leaf and selector moments of a standard Gaussian variable.
--
--   **Statement.** Let $(\Omega_n,P_n)_{n\in\mathbb N}$ be probability spaces and $T_n:\Omega_n\to\mathbb R$ measurable functions such that
--   1. $T_n$ converges in distribution to the standard Gaussian law $\mathcal N(0,1)$;
--   2. $T_n^k$ is $P_n$-integrable for every $n$ and every $k\in\{0,1,2\}$;
--   3. $\int T_n^k\,dP_n\to\int x^k\,d\mathcal N(0,1)(x)$ for $k=0,1,2$, that is, $\mathbb E\,T_n\to0$ and $\mathbb E\,T_n^2\to1$.
--
--   Write $L_n=M^{\ell}$ and $S_n=M^{s}$ for the leaf and selector moments of $T_n$ under $P_n$. Then for all sufficiently large $n$,
--
--   $$
--   \int\ell_i(T_n)\,dP_n>0\ \text{ for every leaf } i\qquad\text{and}\qquad \eta<\mathcal G(L_n,S_n).
--   $$
--
--   For a standardised statistic on a finite uniform space, the gain $\mathcal G$ of its leaf and selector moments is the closed-form value of the deficit of a soft switching event built from the leaf tests and the selector weights. This theorem transfers a strict lower bound for it from the Gaussian model to every sequence of statistics that is asymptotically standard Gaussian in distribution and in its first two moments; the constant $\eta$ is positive, being half of the Gaussian value of the gain. In the construction it is applied to normalised sums of independent copies of a centred, unit-variance statistic.
--
--   **Formalization Note** The grid is `gridN = (2^128)^8`, `radius = 96`, `step = radius / gridN`, `width = 1 / ((2^128)^12)`, the leaves are `Fin (2*gridN+1)`, $\ell_i$ and $s_i$ are `leafTest i` and `selectorTest i` (built from `tent` and `weight`), $M^u_k(i)$ is `moments P T u k i`, and the gain and $\eta$ are `gain` and `eta`. Convergence in distribution is `TendstoInDistribution`. Lean's division by zero returns $0$, but the first conclusion guarantees that the denominators $l_0(i)$ in $\mathcal G(L_n,S_n)$ are positive.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/MomentTransfer.lean#L210-L233

import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_MomentTransfer

open OAI OAI.SquareRootDegree OAI.SquareRootDegree.MomentTransfer
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
open SmoothGaussian SmoothSelector GaussianGain
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem OAI.SquareRootDegree.MomentTransfer.eventually_positive_gain {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T : ∀ n, Ω n → ℝ) (hm : ∀ n, Measurable (T n))
    (hT : TendstoInDistribution T atTop (fun x : ℝ => x) P (gaussianReal 0 1))
    (hi : ∀ n (k : Fin 3), Integrable (fun x => (T n x)^(k:ℕ)) (P n))
    (hM : ∀ k : Fin 3, Tendsto (fun n => ∫ x, (T n x)^(k:ℕ) ∂P n) atTop
      (𝓝 (∫ x : ℝ, x^(k:ℕ) ∂gaussianReal 0 1))) :
    ∀ᶠ n in atTop, (∀ i : Leaves, 0 < moments (P n) (T n) leafTest 0 i) ∧
      eta < gain (moments (P n) (T n) leafTest) (moments (P n) (T n) selectorTest) := by sorry
