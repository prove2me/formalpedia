-- Prove2me | Theorems.Thm_McFadden1974_MLE_strictConcaveOn_L_and_unique_max
-- name    : McFadden1974.MLE.strictConcaveOn_L_and_unique_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:04:30.990544+00:00
-- url     : https://prove2.me/theorems/3f29a1b1-d802-4790-8053-b5e0e1738d6b
-- title:
--   First sentence of p. 116 — a nonsingular Hessian gives a unique maximum
-- statement:
--   Suppose the Hessian $\partial^2 L/\partial\theta\,\partial\theta'$ of the conditional logit log-likelihood (Equation (20)) is nonsingular at every $\theta \in \mathbb{R}^K$. Then $L$ is strictly concave on $\mathbb{R}^K$, and $L$ has at most one maximizer: if $\theta_1$ and $\theta_2$ both satisfy $L(\theta) \le L(\theta_k)$ for all $\theta$, then
--   $$\theta_1 = \theta_2.$$
--
--   Existence of a maximizer is not asserted; it is the subject of Lemma 3. Strict concavity is the property the proof of Lemma 3 invokes.
--
--   **Formalization Note** Nonsingularity is read at every $\theta$, as injectivity of the Hessian's linear map.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 116 (PDF p. 12), first sentence

import Mathlib
import Definitions.Def_McFadden1974_MLE_Model

namespace McFadden1974.MLE

open scoped RealInnerProductSpace

/-- **A nonsingular Hessian gives a unique maximum** (unnumbered, first sentence of p. 116;
McFadden, *Conditional Logit Analysis of Qualitative Choice Behavior*, in P. Zarembka (ed.),
*Frontiers in Econometrics*, Academic Press (1974), p. 116, PDF p. 12): "If, further, the matrix ∂²L/∂θ∂θ' is nonsingular, L has a unique
maximum in θ (provided one exists)."

If the Hessian (20) is nonsingular at every `θ`, then `L` is strictly concave on `ℝ^K` (the
property the proof of Lemma 3 invokes as "L is strictly concave") and any two global maximizers of
`L` coincide.

**Formalization Note.** "Nonsingular" is read at every `θ`, as injectivity of the linear map
`Data.hess d θ`; existence of a maximizer is not asserted. -/
theorem strictConcaveOn_L_and_unique_max
    {K : ℕ} (d : Data K)
    (hnonsing : ∀ θ : EuclideanSpace ℝ (Fin K), Function.Injective (d.hess θ)) :
    StrictConcaveOn ℝ Set.univ d.L ∧
      ∀ θ₁ θ₂ : EuclideanSpace ℝ (Fin K),
        (∀ θ, d.L θ ≤ d.L θ₁) → (∀ θ, d.L θ ≤ d.L θ₂) → θ₁ = θ₂ := by sorry

end McFadden1974.MLE
