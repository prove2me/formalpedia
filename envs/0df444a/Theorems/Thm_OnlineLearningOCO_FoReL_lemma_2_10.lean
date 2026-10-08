-- Prove2me | Theorems.Thm_OnlineLearningOCO_FoReL_lemma_2_10
-- name    : OnlineLearningOCO.FoReL.lemma_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:01.372987+00:00
-- url     : https://prove2.me/theorems/98959aac-f651-4c98-903d-11c99b3528c3
-- title:
--   Lemma 2.10 — FoReL with a σ-strongly-convex regularizer is stable: f_t(w_t) − f_t(w_{t+1}) ≤ L_t²/σ
-- statement:
--   Let $E$ be a real normed space with norm $\|\cdot\|$, $S \subseteq E$, $\sigma > 0$, and let $R$ be $\sigma$-strongly-convex over $S$ with respect to $\|\cdot\|$. Let $w_1, w_2, \dots$ be the predictions of Follow-the-Regularized-Leader with regularizer $R$ on losses $f_1, f_2, \dots$. Fix a round $t \ge 1$ and assume $f_1, \dots, f_t$ are convex on $S$. If $f_t$ is $L_t$-Lipschitz over $S$ with respect to $\|\cdot\|$, i.e. $|f_t(u) - f_t(v)| \le L_t \|u - v\|$ for $u, v \in S$, then
--
--   $$
--   f_t(w_t) - f_t(w_{t+1}) \le L_t \|w_t - w_{t+1}\| \le \frac{L_t^2}{\sigma}.
--   $$
--
--   Together with Lemma 2.3 this bounds the regret of FoReL by $R(u) - R(w_1) + \sum_t L_t^2/\sigma$.
--
--   **Formalization Note** Both inequalities of the chain are stated, as a conjunction. The convexity of $f_1, \dots, f_t$ on $S$ is the standing assumption of online convex optimization (p. 119); the proof uses it to make $\sum_{i<t} f_i + R$ and $\sum_{i \le t} f_i + R$ strongly convex. Strong convexity is Mathlib's `StrongConvexOn S σ R` (see Lemma 2.8), which includes convexity of $S$. The proof on the page ends with "$\|w_t - w_{t+1}\| \le L/\sigma$", a misprint for $L_t/\sigma$; the statement is unaffected.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 137, Lemma 2.10

import Mathlib
import Definitions.Def_OnlineLearningOCO_FoReL_IsFoReLRun

namespace OnlineLearningOCO.FoReL

/-- Lemma 2.10 (Shalev-Shwartz, FnT ML 4(2) (2011), p. 137). Let `R` be `σ`-strongly-convex
over `S` (`σ > 0`) and let `w₁, w₂, …` be the predictions of FoReL on losses convex on `S`. For
a round `t ≥ 1`, if `f_t` is `L_t`-Lipschitz over `S` with respect to `‖·‖`, then
`f_t(w_t) − f_t(w_{t+1}) ≤ L_t ‖w_t − w_{t+1}‖ ≤ L_t² / σ`. -/
theorem lemma_2_10 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (σ : ℝ) (hσ : 0 < σ) (f : ℕ → E → ℝ) (R : E → ℝ) (w : ℕ → E)
    (hR : StrongConvexOn S σ R) (t : ℕ) (ht : 1 ≤ t)
    (hf : ∀ i ∈ Finset.Icc 1 t, ConvexOn ℝ S (f i))
    (Lt : ℝ) (hLip : ∀ u ∈ S, ∀ v ∈ S, |f t u - f t v| ≤ Lt * ‖u - v‖)
    (hw : IsFoReLRun S f R w) :
    f t (w t) - f t (w (t + 1)) ≤ Lt * ‖w t - w (t + 1)‖ ∧
      Lt * ‖w t - w (t + 1)‖ ≤ Lt ^ 2 / σ := by sorry

end OnlineLearningOCO.FoReL
