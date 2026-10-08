-- Prove2me | Theorems.Thm_OnlineLearningOCO_FoReL_theorem_2_11
-- name    : OnlineLearningOCO.FoReL.theorem_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:02.559994+00:00
-- url     : https://prove2.me/theorems/58a96893-4965-418b-a680-a23ad94ad423
-- title:
--   Theorem 2.11 — FoReL with a σ-strongly-convex regularizer: Regret_T(u) ≤ R(u) − min_S R + TL²/σ
-- statement:
--   Let $E$ be a real normed space with norm $\|\cdot\|$, $S \subseteq E$, and $T \ge 1$. Let $f_1, \dots, f_T$ be convex functions on $S$ such that $f_t$ is $L_t$-Lipschitz over $S$ with respect to $\|\cdot\|$, and let $L$ be such that
--
--   $$
--   \frac{1}{T} \sum_{t=1}^{T} L_t^2 \le L^2 .
--   $$
--
--   Assume that Follow-the-Regularized-Leader, $w_t \in \operatorname{argmin}_{w \in S} \sum_{i<t} f_i(w) + R(w)$, is run on the sequence with a regularization function $R$ that is $\sigma$-strongly-convex over $S$ with respect to the same norm, $\sigma > 0$. Then for all $u \in S$,
--
--   $$
--   \mathrm{Regret}_T(u) = \sum_{t=1}^{T} f_t(w_t) - \sum_{t=1}^{T} f_t(u) \le R(u) - \min_{v \in S} R(v) + \frac{T L^2}{\sigma}.
--   $$
--
--   This is the survey's central regret bound for FoReL. Choosing $R(w) = \frac{1}{2\eta}\|w\|_2^2$ gives online gradient descent's $\frac{1}{2\eta}\|u\|_2^2 + \eta T L^2$ (Corollary 2.12), and an entropic regularizer gives the experts bounds (Corollary 2.14).
--
--   **Formalization Note** $\min_{v \in S} R(v)$ is written as the infimum of $R(S)$; a FoReL run exists only if $R$ attains its minimum on $S$ at $w_1$, so the infimum is that minimum. The hypothesis $T \ge 1$ is needed only for the factor $1/T$. Convexity and Lipschitzness are assumed for $t = 1, \dots, T$, the rounds of the regret; the losses of later rounds are unconstrained. Strong convexity is Mathlib's `StrongConvexOn S σ R` (see Lemma 2.8), which includes convexity of $S$. The carrier is an arbitrary real normed space, so the theorem covers every norm, e.g. $\ell_1$ on $\mathbb R^d$ as used in Corollary 2.14. The bound is explicit on the page; no $O(\cdot)$ is involved.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 138, Theorem 2.11

import Mathlib
import Definitions.Def_OnlineLearningOCO_FoReL_regret
import Definitions.Def_OnlineLearningOCO_FoReL_IsFoReLRun

namespace OnlineLearningOCO.FoReL

/-- Theorem 2.11 (Shalev-Shwartz, FnT ML 4(2) (2011), p. 138). Let `f_1, …, f_T` be convex
functions on `S` with `f_t` `L_t`-Lipschitz over `S` with respect to a norm `‖·‖`, and let `L`
satisfy `(1/T) ∑_{t=1}^T L_t² ≤ L²`. If FoReL is run on the sequence with a regularization
function `R` that is `σ`-strongly-convex over `S` with respect to the same norm (`σ > 0`), then
for all `u ∈ S`, `Regret_T(u) ≤ R(u) − min_{v ∈ S} R(v) + T L² / σ`.
`min_{v ∈ S} R(v)` is written `sInf (R '' S)`; it is attained at `w 1`. -/
theorem theorem_2_11 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (σ : ℝ) (hσ : 0 < σ) (f : ℕ → E → ℝ) (R : E → ℝ) (w : ℕ → E)
    (hR : StrongConvexOn S σ R) (T : ℕ) (hT : 0 < T)
    (hf : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ S (f t))
    (Lt : ℕ → ℝ)
    (hLip : ∀ t ∈ Finset.Icc 1 T, ∀ u ∈ S, ∀ v ∈ S, |f t u - f t v| ≤ Lt t * ‖u - v‖)
    (L : ℝ) (hL : (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, Lt t ^ 2 ≤ L ^ 2)
    (hw : IsFoReLRun S f R w) :
    ∀ u ∈ S, regret f w T u ≤ R u - sInf (R '' S) + T * L ^ 2 / σ := by sorry

end OnlineLearningOCO.FoReL
