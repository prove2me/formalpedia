-- Prove2me | Theorems.Thm_NewsBundling_Unilateral_lemma3_platform
-- name    : NewsBundling.Unilateral.lemma3_platform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:45.945731+00:00
-- url     : https://prove2.me/theorems/8dd647e0-fda6-4e5d-9c14-5a01e430b51e
-- title:
--   Lemma 3, p. 11 — platform news share
-- statement:
--   Under Table 1's standing assumptions, let $\sigma$ be any subgame-perfect equilibrium. At each quality $q\in[0,1)$, the platform's news share is
--
--   $$\lambda(q)=\min\{q,\Lambda\}.$$
--
--   This determines the second-stage response used to calculate the publisher's payoff.
--
--   **Formalization Note** At $q=1$ all feasible platform shares yield zero platform time, so the platform is indifferent. The theorem therefore excludes that endpoint; this does not affect the publisher's payoff there.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), p. 11, Lemma 3

import Mathlib
import Definitions.Def_NewsBundling_Unilateral_Setting

namespace NewsBundling.Unilateral

/-- Lemma 3, p. 11: every platform best response is min(q, Λ) away from q = 1. -/
theorem lemma3_platform (β φ0 φ1 c Λ : ℝ)
    (h : StandingAssumptions β φ0 φ1 c Λ) :
    ∀ σ, IsSPE β φ0 φ1 c Λ σ →
      ∀ q ∈ Set.Ico (0 : ℝ) 1, σ.platform q = min q Λ := by sorry

end NewsBundling.Unilateral
