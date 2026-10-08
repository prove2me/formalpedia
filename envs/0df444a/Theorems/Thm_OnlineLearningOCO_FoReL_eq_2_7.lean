-- Prove2me | Theorems.Thm_OnlineLearningOCO_FoReL_eq_2_7
-- name    : OnlineLearningOCO.FoReL.eq_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:48.608521+00:00
-- url     : https://prove2.me/theorems/caffa680-587d-475c-acf5-ea980f652cc9
-- title:
--   Eq. (2.7) — consecutive FoReL predictions: σ‖w_t − w_{t+1}‖² ≤ f_t(w_t) − f_t(w_{t+1})
-- statement:
--   Let $E$ be a real normed space, $S \subseteq E$, and let the regularization function $R$ be $\sigma$-strongly-convex over $S$. Fix a round $t \ge 1$, assume $f_1, \dots, f_t$ are convex on $S$, and let $w_1, w_2, \dots$ be a run of Follow-the-Regularized-Leader on $f$ with regularizer $R$. Then
--
--   $$
--   \sigma \|w_t - w_{t+1}\|^2 \le f_t(w_t) - f_t(w_{t+1}).
--   $$
--
--   This is equation (2.7) in the proof of Lemma 2.10: the objectives $F_t = \sum_{i<t} f_i + R$ and $F_{t+1}$ are both $\sigma$-strongly convex, and comparing each at the other's minimizer gives the display.
--
--   **Formalization Note** Strong convexity is Mathlib's `StrongConvexOn S σ R` (see Lemma 2.8). Convexity is required of $f_1, \dots, f_t$ on $S$ only, the losses that enter $F_t$ and $F_{t+1}$. No sign condition on $\sigma$ is imposed.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 138, §2.5.2, proof of Lemma 2.10, eq. (2.7)

import Mathlib
import Definitions.Def_OnlineLearningOCO_FoReL_IsFoReLRun

namespace OnlineLearningOCO.FoReL

/-- Equation (2.7) (Shalev-Shwartz, FnT ML 4(2) (2011), §2.5.2, proof of Lemma 2.10, p. 138).
Let `R` be `σ`-strongly-convex over `S`, let `f_1, …, f_t` be convex on `S`, and let
`w₁, w₂, …` be a run of FoReL. Then `σ ‖w_t − w_{t+1}‖² ≤ f_t(w_t) − f_t(w_{t+1})`. -/
theorem eq_2_7 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (σ : ℝ) (f : ℕ → E → ℝ) (R : E → ℝ) (w : ℕ → E)
    (hR : StrongConvexOn S σ R) (t : ℕ) (ht : 1 ≤ t)
    (hf : ∀ i ∈ Finset.Icc 1 t, ConvexOn ℝ S (f i))
    (hw : IsFoReLRun S f R w) :
    σ * ‖w t - w (t + 1)‖ ^ 2 ≤ f t (w t) - f t (w (t + 1)) := by sorry

end OnlineLearningOCO.FoReL
