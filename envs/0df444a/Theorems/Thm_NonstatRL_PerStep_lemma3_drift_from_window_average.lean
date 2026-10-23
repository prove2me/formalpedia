-- Prove2me | Theorems.Thm_NonstatRL_PerStep_lemma3_drift_from_window_average
-- name    : NonstatRL.PerStep.lemma3_drift_from_window_average
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:25.55327+00:00
-- url     : https://prove2.me/theorems/e3cfda4c-7d8a-405b-83ea-167e9f577ae4
-- title:
--   Lemma 3 — drift from a visited-pair window average
-- statement:
--   Consider an episode starting at $\tau(m)$ and a later round $t$. At any allowed state-action pair $(s,a)$ visited at least once during the episode-start window, the reward and transition averages from that window differ from their round-$t$ values by at most the accumulated variation:
--
--   $$
--   |r_t(s,a)-\bar r_{\tau(m)}(s,a)|\le\operatorname{var}_{r,t},\qquad
--   \|p_t(\cdot\mid s,a)-\bar p_{\tau(m)}(\cdot\mid s,a)\|_1\le\operatorname{var}_{p,t}.
--   $$
--
--   The lemma converts temporal drift into estimator error for visited pairs. **Formalization Note** The paper states the claim for every pair, but its zero-at-unvisited convention makes that false. The positive visit count is an explicit pin. The average is over actual visits, not a uniform average of window times.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 38, Lemma 3 (pinned visit count)

import Mathlib
import Definitions.Def_NonstatRL_PerStep_Window

open BanditAlgorithm

namespace NonstatRL.PerStep

theorem lemma3_drift_from_window_average {S A : ℕ}
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (W τm t T : ℕ)
    (ht : τm ≤ t ∧ t < T) (s : Fin S) (a : Fin A) (ha : a ∈ As s)
    (hcount : 0 < count st ac (τm - W) τm s a) :
    |(M t).r s a - rBar M st ac (τm - W) τm s a| ≤
        varR M As (τm - W) t ∧
    (∑ s' : Fin S,
      |((M t).P s a s' : ℝ) - pBar M st ac (τm - W) τm s a s'|) ≤
        varP M As (τm - W) t := by sorry

end NonstatRL.PerStep
