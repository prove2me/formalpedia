-- Prove2me | Theorems.Thm_OnlineLearningOCO_Winnow_lemma_2_20
-- name    : OnlineLearningOCO.Winnow.lemma_2_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:20.247994+00:00
-- url     : https://prove2.me/theorems/77770cac-c351-426d-9d63-e75e898515a2
-- title:
--   Lemma 2.20 — OMD with link $\nabla R^\star$: regret $\le R(u)-R(w_1)+\sum_t D_{R^\star}(-z_{1:t}\|-z_{1:t-1})$
-- statement:
--   Let $E$ be a real Hilbert space, $S\subseteq E$, $R:E\to\mathbb R$ (equal to $+\infty$ off $S$ in the paper's convention), and let $R^\star(\theta)=\sup_{w\in S}(\langle w,\theta\rangle-R(w))$ be its conjugate. Suppose the link function $g:E\to E$ satisfies $g=\nabla R^\star$ in the following sense: for every $\theta$, $g(\theta)\in S$, $g(\theta)$ attains the supremum defining $R^\star(\theta)$, and $R^\star$ is differentiable at $\theta$ with gradient $g(\theta)$. Run Online Mirror Descent with link $g$ on linear losses $z_1,\dots,z_T\in E$, so $w_t=g(-z_{1:t-1})$. Then for every $u\in S$,
--   $$\sum_{t=1}^T\langle w_t-u,z_t\rangle\le R(u)-R(w_1)+\sum_{t=1}^T D_{R^\star}\bigl(-z_{1:t}\,\|\,-z_{1:t-1}\bigr),$$
--   and equality holds when $u\in S$ minimizes $R(v)+\sum_{t=1}^T\langle v,z_t\rangle$ over $v\in S$.
--
--   The lemma reduces the regret analysis of OMD to bounding one Bregman divergence of the conjugate per round; Theorem 2.23 applies it to the unnormalized entropy, and through it Winnow's mistake bound follows.
--
--   **Formalization Note** The paper's "$g=\nabla R^\star$" (via Lemma 2.19 and (2.13), cited rather than proved) is encoded by three hypotheses: $g(\theta)\in S$, attainment of the supremum at $g(\theta)$, and `HasGradientAt` of $R^\star$ with gradient $g(\theta)$. The comparator $u$ ranges over $S$, where $R$ is finite. Rounds are numbered $0,\dots,T-1$, and $w_1$ is `omdIterate g z 0`. A copy of this lemma is also drafted in the Normalized EG mission of the same series.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 150, Lemma 2.20

import Mathlib
import Definitions.Def_OnlineLearningOCO_Winnow_OMDDuality
open Finset
open scoped InnerProductSpace

namespace OnlineLearningOCO.Winnow

/-- Lemma 2.20 (p. 150). Online Mirror Descent with link function `g = ∇R⋆` on linear losses
`z_t`: for every `u ∈ S`,
`∑_{t} ⟨w_t - u, z_t⟩ ≤ R(u) - R(w₁) + ∑_{t} D_{R⋆}(-z_{1:t} ‖ -z_{1:t-1})`,
with equality when `u` minimizes `R(v) + ∑_t ⟨v, z_t⟩` over `S`. Rounds are numbered from `0`.
"`g = ∇R⋆`" is encoded by: `g θ ∈ S`, `g θ` attains `sup_{w ∈ S} (⟨w, θ⟩ - R w)` (2.8), (2.13), and
`R⋆` has gradient `g θ` at every `θ`. -/
theorem lemma_2_20 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : Set E) (R : E → ℝ) (g : E → E) (z : ℕ → E)
    (hgS : ∀ θ, g θ ∈ S)
    (hgmax : ∀ θ, ∀ w ∈ S, ⟪w, θ⟫_ℝ - R w ≤ ⟪g θ, θ⟫_ℝ - R (g θ))
    (hgrad : ∀ θ, HasGradientAt (conjOn S R) (g θ) θ) (T : ℕ) :
    (∀ u ∈ S, ∑ t ∈ range T, ⟪omdIterate g z t - u, z t⟫_ℝ ≤
        R u - R (omdIterate g z 0) +
          ∑ t ∈ range T, bregmanDiv (conjOn S R) g
            (-(∑ s ∈ range (t + 1), z s)) (-(∑ s ∈ range t, z s))) ∧
    (∀ u ∈ S, (∀ v ∈ S, R u + ∑ t ∈ range T, ⟪u, z t⟫_ℝ ≤ R v + ∑ t ∈ range T, ⟪v, z t⟫_ℝ) →
      ∑ t ∈ range T, ⟪omdIterate g z t - u, z t⟫_ℝ =
        R u - R (omdIterate g z 0) +
          ∑ t ∈ range T, bregmanDiv (conjOn S R) g
            (-(∑ s ∈ range (t + 1), z s)) (-(∑ s ∈ range t, z s))) := by sorry

end OnlineLearningOCO.Winnow
