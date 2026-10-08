-- Prove2me | Theorems.Thm_OnlineLearningOCO_FoReL_lemma_2_8
-- name    : OnlineLearningOCO.FoReL.lemma_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:32.829658+00:00
-- url     : https://prove2.me/theorems/587c3460-8c3c-4b39-8ea4-793fa31e7314
-- title:
--   Lemma 2.8 — quadratic growth of a strongly convex function at its minimizer
-- statement:
--   Let $E$ be a real normed space with norm $\|\cdot\|$, let $S \subseteq E$ be a nonempty convex set and let $f : S \to \mathbb R$ be $\sigma$-strongly-convex over $S$ with respect to $\|\cdot\|$. Let $w \in S$ be a minimizer of $f$ over $S$. Then for all $u \in S$,
--
--   $$
--   f(u) - f(w) \ge \frac{\sigma}{2} \|u - w\|^2.
--   $$
--
--   This quadratic growth is what makes strongly convex regularizers stabilize Follow-the-Regularized-Leader (Lemma 2.10).
--
--   **Formalization Note** $\sigma$-strong convexity is Mathlib's `StrongConvexOn S σ f`: $S$ is convex and $f(a x + b y) \le a f(x) + b f(y) - a b \frac{\sigma}{2}\|x-y\|^2$ for $x, y \in S$, $a, b \ge 0$, $a + b = 1$. The paper's Definition 2.4 is the subgradient form $f(u) \ge f(w) + \langle z, u - w\rangle + \frac{\sigma}{2}\|u-w\|^2$ for all $z \in \partial f(w)$; it needs a dual pairing that a general normed space does not carry, and it is vacuous at points with no subgradient. The two agree for convex functions that have subgradients on $S$. Nonemptiness of $S$ is witnessed by $w \in S$. No sign condition on $\sigma$ is imposed; the inequality holds for every real $\sigma$.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 135, Lemma 2.8 (strong convexity: Definition 2.4, p. 135)

import Mathlib

namespace OnlineLearningOCO.FoReL

/-- Lemma 2.8 (Shalev-Shwartz, FnT ML 4(2) (2011), p. 135). Let `S` be a nonempty convex set
and `f` a `σ`-strongly-convex function over `S` with respect to the norm `‖·‖`. Let `w` be a
minimizer of `f` over `S`. Then for all `u ∈ S`, `f(u) − f(w) ≥ σ/2 ‖u − w‖²`.
Strong convexity is Mathlib's `StrongConvexOn S σ f`, which includes convexity of `S`;
nonemptiness of `S` is witnessed by `w ∈ S`. -/
theorem lemma_2_8 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (σ : ℝ) (f : E → ℝ) (hf : StrongConvexOn S σ f)
    (w : E) (hwS : w ∈ S) (hwmin : ∀ v ∈ S, f w ≤ f v) :
    ∀ u ∈ S, σ / 2 * ‖u - w‖ ^ 2 ≤ f u - f w := by sorry

end OnlineLearningOCO.FoReL
