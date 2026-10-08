-- Prove2me | Theorems.Thm_OnlineLearningOCO_NormalizedEG_lemma_2_20
-- name    : OnlineLearningOCO.NormalizedEG.lemma_2_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:57.323111+00:00
-- url     : https://prove2.me/theorems/f2cd461b-78b5-4b95-9a2f-b8ca2f39af2a
-- title:
--   Lemma 2.20 — the regret of OMD with link ∇R⋆ is R(u) − R(w₁) plus the Bregman terms of R⋆
-- statement:
--   Let $E$ be a real Hilbert space, $S \subseteq E$, $R : E \to \mathbb R$ a regularizer (taken to be $+\infty$ off $S$), and let $R^\star(\theta) = \sup_{w\in S}(\langle w,\theta\rangle - R(w))$ be its Fenchel conjugate. Let $g : E \to E$ be a link function with $g = \nabla R^\star$, in the sense that for every $\theta \in E$:
--
--   1. $g(\theta) \in S$;
--   2. $g(\theta)$ attains the supremum: $\langle w,\theta\rangle - R(w) \le \langle g(\theta),\theta\rangle - R(g(\theta))$ for every $w \in S$ (that is, $g(\theta) = \operatorname{argmax}_w(\langle w,\theta\rangle - R(w))$, (2.8) and (2.13));
--   3. $R^\star$ is differentiable at $\theta$ with gradient $g(\theta)$.
--
--   Run Online Mirror Descent with link $g$ on linear losses $f_t(w) = \langle w, z_t\rangle$, $z_t \in E$, so that $w_t = g(-z_{1:t-1})$. Then for every $T$ and every $u \in S$,
--   $$\sum_{t=1}^T \langle w_t - u, z_t\rangle \le R(u) - R(w_1) + \sum_{t=1}^T D_{R^\star}(-z_{1:t} \,\|\, -z_{1:t-1}),$$
--   and equality holds for every $u \in S$ that minimizes $R(u) + \sum_{t=1}^T \langle u, z_t\rangle$ over $S$.
--
--   This is the general regret identity for Online Mirror Descent by duality; it reduces the analysis of a specific algorithm to bounding the Bregman divergences of the conjugate, which is how Theorem 2.22 is proved.
--
--   **Formalization Note** Rounds are numbered from $0$: Lean's `omdIterate g z t = g(-∑_{s<t} z s)` is the paper's $w_{t+1}$, and `omdIterate g z 0 = g 0` is $w_1$. The paper's $R$ equals $+\infty$ off $S$; here $R$ is real-valued and the comparator $u$ and the minimizer range over $S$ only, which is the same statement. The phrase "$g = \nabla R^\star$" is encoded by the three hypotheses above; differentiability of $R^\star$ is the paper's standing consequence of Lemma 2.19 and is assumed, not derived. The same lemma is also drafted, independently, by the Winnow mission of this series.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 150, Lemma 2.20

import Mathlib
import Definitions.Def_OnlineLearningOCO_NormalizedEG_Duality
open scoped RealInnerProductSpace

namespace OnlineLearningOCO.NormalizedEG

/-- Lemma 2.20, p. 150. Online Mirror Descent with link function `g = ∇R⋆` (where `R⋆` is the
Fenchel conjugate of `R + I_S`) has regret, against every `u ∈ S`,
`∑_{t=1}^T ⟨w_t − u, z_t⟩ ≤ R(u) − R(w_1) + ∑_{t=1}^T D_{R⋆}(−z_{1:t} ‖ −z_{1:t−1})`,
with equality for a `u ∈ S` minimizing `R(u) + ∑_t ⟨u, z_t⟩` over `S`.
"`g = ∇R⋆`" is encoded by: `g` maps into `S`; `g θ` attains the supremum defining `R⋆(θ)`
((2.8)/(2.13)); and `g θ` is the gradient of `R⋆` at `θ`. Rounds are 0-based. -/
theorem lemma_2_20 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : Set E) (R : E → ℝ) (g : E → E) (z : ℕ → E)
    (hgS : ∀ θ, g θ ∈ S)
    (hgmax : ∀ θ, ∀ w ∈ S, ⟪w, θ⟫ - R w ≤ ⟪g θ, θ⟫ - R (g θ))
    (hgrad : ∀ θ, HasGradientAt (fenchelConj S R) (g θ) θ)
    (T : ℕ) :
    (∀ u ∈ S,
      ∑ t ∈ Finset.range T, ⟪omdIterate g z t - u, z t⟫ ≤
        R u - R (omdIterate g z 0) +
          ∑ t ∈ Finset.range T,
            bregman (fenchelConj S R) g (-(cumSum z (t + 1))) (-(cumSum z t))) ∧
    (∀ u ∈ S,
      (∀ v ∈ S, R u + ∑ t ∈ Finset.range T, ⟪u, z t⟫ ≤ R v + ∑ t ∈ Finset.range T, ⟪v, z t⟫) →
      ∑ t ∈ Finset.range T, ⟪omdIterate g z t - u, z t⟫ =
        R u - R (omdIterate g z 0) +
          ∑ t ∈ Finset.range T,
            bregman (fenchelConj S R) g (-(cumSum z (t + 1))) (-(cumSum z t))) := by sorry

end OnlineLearningOCO.NormalizedEG
