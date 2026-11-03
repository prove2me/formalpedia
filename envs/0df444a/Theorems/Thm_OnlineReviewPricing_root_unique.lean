-- Prove2me | Theorems.Thm_OnlineReviewPricing_root_unique
-- name    : OnlineReviewPricing.root_unique
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:40.987991+00:00
-- url     : https://prove2.me/theorems/aa2468a3-8b7d-4d3d-b274-5f93a939c74d
-- title:
--   (EC.15), p.ec8 — under (15), $g$ is an increasing bijection and (14) has a unique root
-- statement:
--   Let $\gamma,T>0$ and assume condition (15),
--
--   $$
--   \frac{\gamma T(\mu-\mu_0)}{4(1+\gamma T)}<1 .
--   $$
--
--   Then the function
--
--   $$
--   g(z)=z+\exp(z)-\mu+1-\frac{\mu_0-\mu}{\gamma\ell(z)T+1}
--   $$
--
--   is strictly increasing and onto $\mathbb R$, and equation (14) has exactly one root.
--
--   Condition (15) always holds when $\mu_0\ge\mu$, and it holds when $\mu-\mu_0\le 4$. Without it, (14) can have several roots.
--
--   Differences from the source: none.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.15) and the end of the proof of Theorem 1, p.ec8 (PDF 45)

import Mathlib
import Definitions.Def_OnlineReviewPricing_rootFunction
import Definitions.Def_OnlineReviewPricing_IsRootOf14

namespace OnlineReviewPricing

/-- Under condition (15), the function `g` of (EC.15) is strictly increasing and onto `ℝ`, and
equation (14) has exactly one root (Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), p.ec8). -/
theorem root_unique (μ μ₀ γ T : ℝ) (hγ : 0 < γ) (hT : 0 < T)
    (h15 : γ * T * (μ - μ₀) / (4 * (1 + γ * T)) < 1) :
    StrictMono (rootFunction μ μ₀ γ T) ∧ Function.Surjective (rootFunction μ μ₀ γ T) ∧
      ∃! z, IsRootOf14 μ μ₀ γ T z := by sorry

end OnlineReviewPricing
