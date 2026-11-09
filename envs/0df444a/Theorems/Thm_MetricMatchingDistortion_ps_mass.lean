-- Prove2me | Theorems.Thm_MetricMatchingDistortion_ps_mass
-- name    : MetricMatchingDistortion.ps_mass
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:17:27.551897+00:00
-- url     : https://prove2.me/theorems/d3206cf4-fd65-4738-a583-ffede47058fe
-- title:
--   §3.3 and Equation (65) — PS rows sum to $t$, $\sum_b q_b(t)=n(1-t)$, unmatched mass $k$
-- statement:
--   Let $X(t)$ be the Probabilistic Serial matrix after $t$ units of time and $q_b(t)=1-\sum_aX_{a,b}(t)$. For every $n\ge1$, every ranking profile and every $t\in[0,1]$:
--   1. $X(t)$ is a partial fractional matching;
--   2. every row of $X(t)$ sums to $t$;
--   3. $\sum_{b}q_b(t)=n(1-t)$ (Equation (65)).
--
--   Consequently, for every real $0<k\le n$, the prefix $X(1-k/n)$ has unmatched mass exactly $k$.
--
--   These mass facts make the stopped PS prefix a valid input to the completion of Lemma 3.1.
--
--   Differences from the source:
--   - encoding: X(t) = PS run for t units of time (Algorithm 7) → psAlloc: the eating step ExAnteExPost.RPS.eatStep with favorite-available-item picks, iterated n+1 times from capacities 1, the zero matrix and time budget t; reason: every step but the last exhausts an item, so n+1 steps run PS to time t
--   - encoding: n ≥ 1 (standing, §2 p.9) → [NeZero n]; reason: the same condition as a type class
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), §3.3, p.17 (PDF p.19); §6.2.1, p.51 (PDF p.53), Equation (65)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsPartialFractionalMatching
import Definitions.Def_MetricMatchingDistortion_psAlloc

namespace MetricMatchingDistortion

/-- **Mass of the Probabilistic Serial prefix.** Charikar et al., *Sublinear Metric Distortion for Matching*, arXiv:2611.05777 (held version,
sha256 fdf3452b…), §3.3, p.17 (PDF p.19): "Let X(t) denote the partial fractional matching obtained by running PS
for t units of time. Every row of X(t) sums to t. Thus, for any real 0 < k ≤ n, stopping at time
1 − k/n leaves unmatched mass k." §6.2.1, p.51 (PDF p.53), Equation (65): "agents eat at total
rate n and the total capacity is n, so ∑_{b∈B} q_b(t) = n(1 − t) for every t ∈ [0, 1]".

For `t ∈ [0, 1]`: `X(t)` is a partial fractional matching, every row sums to `t`, and the
remaining capacities sum to `n(1 − t)`; for every real `0 < k ≤ n`, `X(1 − k/n)` has unmatched
mass `k`. -/
theorem ps_mass (n : ℕ) [NeZero n] (rk : Ranking n) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      IsPartialFractionalMatching (psAlloc rk t) ∧ (∀ a, ∑ b, psAlloc rk t a b = t) ∧
        ∑ b, remaining rk t b = n * (1 - t)) ∧
      ∀ k : ℝ, 0 < k → k ≤ n → unmatchedMass (psAlloc rk (1 - k / n)) = k := by sorry

end MetricMatchingDistortion
