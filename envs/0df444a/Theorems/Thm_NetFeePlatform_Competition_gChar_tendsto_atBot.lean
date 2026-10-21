-- Prove2me | Theorems.Thm_NetFeePlatform_Competition_gChar_tendsto_atBot
-- name    : NetFeePlatform.Competition.gChar_tendsto_atBot
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:54.677464+00:00
-- url     : https://prove2.me/theorems/94ca1ba3-c8d5-4138-8c5b-7955bb7a84fa
-- title:
--   Proof of Proposition 4, p. 49 — lim_{n→0} g(n; J) = −∞
-- statement:
--   For every $\gamma\in\mathbb R$ and every $J\ge2$, the characterization function
--   $$g(n;J)=\ln n-\ln(J-1)-\ln(1-n)+\frac{1}{1-\frac{n}{J-1}}-2\gamma\frac{n}{J-1}-\Big(\frac1n-2\gamma(1-n)\Big)$$
--   satisfies
--   $$\lim_{n\to0^+}g(n;J)=-\infty.$$
--
--   Together with a point where $g(\cdot;J)$ is positive, this limit is what the intermediate value theorem needs to produce a zero, i.e. an equilibrium with a dominant platform.
--
--   **Formalization Note** The limit is taken from the right, along $n>0$.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 49, Appendix E.2, proof of Proposition 4

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_Competition_GChar

namespace NetFeePlatform.Competition
theorem gChar_tendsto_atBot (γ : ℝ) (J : ℕ) (hJ : 2 ≤ J) :
    Filter.Tendsto (gChar γ J) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by sorry
end NetFeePlatform.Competition
