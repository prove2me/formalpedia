-- Prove2me | Theorems.Thm_OptimalBAI_TrackStop_c_tracking_bounds
-- name    : OptimalBAI.TrackStop.c_tracking_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:15:16.335156+00:00
-- url     : https://prove2.me/theorems/2d954200-659e-46a1-8826-ba4ac3dba241
-- title:
--   Lemma 7 — C-Tracking guarantees
-- statement:
--   Consider a $K$-armed bandit trajectory whose arms follow the C-Tracking rule, for a target map $w^*$ with values in the simplex $\Sigma_K$, any choice of $L^\infty$ projections $w^\epsilon$ onto $\Sigma^\epsilon_K$ and any tie-breaking. Let $N_a(t)$ be the number of draws of arm $a$ in the first $t$ rounds and $\hat{\boldsymbol\mu}(s)$ the vector of empirical means after $s$ rounds. Then for all $t\ge1$ and every arm $a$,
--   $$N_a(t)\ge\sqrt{t+K^2}-2K\qquad\text{and}\qquad\max_{1\le a\le K}\Big|N_a(t)-\sum_{s=0}^{t-1}w^*_a(\hat{\boldsymbol\mu}(s))\Big|\le K(1+\sqrt t).$$
--
--   The first bound says every arm is explored at rate $\sqrt t$; the second says the counts track the cumulated plug-in proportions up to $O(\sqrt t)$.
--
--   **Formalization Note** The statement is pathwise: it holds on every trajectory that follows the rule, with no probability involved. An arm not yet drawn has empirical mean $0$; the target map may take any value in $\Sigma_K$ there.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 7, Lemma 7 (proof: App. B.1, p. 20)

import Mathlib
import Definitions.Def_OptimalBAI_TrackStop_Tracking

open BanditAlgorithm

namespace OptimalBAI.TrackStop

/-- Lemma 7 (Garivier–Kaufmann, arXiv:1602.04589v2, p. 7). Along any trajectory that follows
C-Tracking (for any target map `wt` with values in `Σ_K`, any choice of `L^∞` projections and any
tie-breaking), for every `t ≥ 1` and every arm `a`,
`N_a(t) ≥ √(t + K²) - 2K` and `|N_a(t) - ∑_{s=0}^{t-1} w*_a(μ̂(s))| ≤ K(1 + √t)`,
where `w*(μ̂(s))` is the target map at the empirical means after `s` rounds. -/
theorem c_tracking_bounds {K : ℕ} (wt : (Fin K → ℝ) → (Fin K → ℝ))
    (hwt_simplex : ∀ μ', wt μ' ∈ simplex K)
    (ω : ℕ → Fin K × ℝ) (hω : FollowsCTracking wt ω) :
    ∀ t : ℕ, 1 ≤ t → ∀ a : Fin K,
      Real.sqrt ((t : ℝ) + (K : ℝ) ^ 2) - 2 * (K : ℝ) ≤ (trajPullCount a t ω : ℝ) ∧
      |(trajPullCount a t ω : ℝ) - ∑ s ∈ Finset.range t, wt (trajMeanVec s ω) a| ≤
        (K : ℝ) * (1 + Real.sqrt (t : ℝ)) := by sorry

end OptimalBAI.TrackStop
