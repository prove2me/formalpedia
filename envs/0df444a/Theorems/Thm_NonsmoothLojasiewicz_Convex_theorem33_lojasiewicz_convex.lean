-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Convex_theorem33_lojasiewicz_convex
-- name    : NonsmoothLojasiewicz.Convex.theorem33_lojasiewicz_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:12:53.400015+00:00
-- url     : https://prove2.me/theorems/d3eade6b-78a1-42ac-b2ca-f61e88c02866
-- title:
--   Theorem 3.3: Łojasiewicz inequality for lsc convex subanalytic $f$ on bounded sets
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be a lower semicontinuous convex subanalytic function with $\operatorname{crit} f\neq\emptyset$. For any bounded set $K\subseteq\mathbb R^n$ there exists an exponent $\theta\in[0,1)$ such that the function
--   $$\frac{|f-\min f|^{\theta}}{m_f}\tag{14}$$
--   is bounded on $K$; that is, there is a constant $C$ with
--   $$|f(x)-\min f|^{\theta}\le C\,\|x^*\|\qquad\text{for all }x\in K\text{ and all }x^*\in\partial f(x).$$
--
--   Here $\partial f$ is the limiting subdifferential and $m_f(x)=\inf\{\|x^*\|:x^*\in\partial f(x)\}$ the nonsmooth slope. Unlike Theorem 3.1, the inequality holds uniformly on any bounded set, not only near a critical point, and it requires neither continuity of $f$ on its domain nor a closed domain. The exponent $\theta$ may depend on $K$.
--
--   **Formalization Note** "Lower semicontinuous, convex, somewhere finite, never $-\infty$" is the published `GammaZero`; $\partial f$ is the published `LimitingSubdiff`. The bounded ratio is encoded without division under the paper's conventions $0^0=1$ and $\infty/\infty=0/0=0$: at points with $\partial f(x)=\emptyset$ (in particular outside $\operatorname{dom} f$) the ratio is $0$, and at points with a subgradient $f(x)$ is finite, so `toReal` is faithful. $\min f$ is $\inf_y f(y)$ in `EReal`, finite and attained because $\operatorname{crit} f\neq\emptyset$. The power is `Real.rpow`.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1215, Theorem 3.3, ratio (14)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit

open Filter Topology
open NonconvexSplitting.Shared MoreauProx.Characterization

namespace NonsmoothLojasiewicz.Convex

/-- Theorem 3.3 of Bolte–Daniilidis–Lewis (p. 1215): let `f : ℝⁿ → ℝ ∪ {+∞}` be a lower
semicontinuous convex subanalytic function with `crit f ≠ ∅`. For any bounded set `K` there is an
exponent `θ ∈ [0, 1)` such that `|f − min f|^θ / m_f` (14) is bounded on `K`: there is `C` with
`|f(x) − min f|^θ ≤ C ‖x*‖` for every `x ∈ K` and every limiting subgradient `x* ∈ ∂f(x)`.
(At points with `∂f(x) = ∅`, `m_f(x) = +∞` and the ratio is `0` by the paper's conventions.) -/
theorem theorem33_lojasiewicz_convex {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) (hsub : NonsmoothLojasiewicz.Continuous.IsSubanalyticFn f) (hcrit : (crit f).Nonempty)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : Bornology.IsBounded K) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∃ C : ℝ, ∀ x ∈ K, ∀ v ∈ LimitingSubdiff f x,
      |(f x).toReal - (⨅ y, f y).toReal| ^ θ ≤ C * ‖v‖ := by sorry

end NonsmoothLojasiewicz.Convex
