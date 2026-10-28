-- Prove2me | Theorems.Thm_OfflineStochMatch_Attenuation_eq_22
-- name    : OfflineStochMatch.Attenuation.eq_22
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:59.246213+00:00
-- url     : https://prove2.me/theorems/64eac0af-65a5-4366-a898-3208f54e0b0a
-- title:
--   Eq. (22), p. 15 — ã(y_e)∫₀¹(e^{−x(2−y_e)} + xe^{−x(2−y_e)})² dx is minimized at y_e = 0, where it equals β*
-- statement:
--   Let $\tilde a$ be the exponential ($\tilde a(z) = e^{-z/2}$) or the linear ($\tilde a(z) = 1 - z/2$) attenuation function with $\alpha = 1/2$. For $y_e \in [0,1]$ put
--   $$F(y_e) = \tilde a(y_e) \int_0^1 \left(e^{-x(2-y_e)} + x e^{-x(2-y_e)}\right)^2 dx. \tag{22}$$
--   Then $F(y_e) \ge \beta^*$ for every $y_e \in [0,1]$, and $F(0) = \beta^* = \int_0^1 (e^{-2x} + x e^{-2x})^2\,dx$.
--
--   Display (22) is the lower bound the proof of Theorem 1 reaches in the case where both endpoints of $e$ have patience $2$, and this is the case in which the constant $\beta^*$ of Theorem 1 is attained.
--
--   **Formalization Note** The two clauses state the page's "minimized when $y_e = 0$, in which case we get a lower bound of exactly $\beta^*$": the minimum value over $[0,1]$ is $\beta^*$, attained at $0$.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 15, Eq. (22) and the sentence after it (β* from Eq. (5), p. 9)

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting

namespace OfflineStochMatch.Attenuation

theorem eq_22 (aT : ℝ → ℝ) (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) :
    (∀ ye ∈ Set.Icc (0 : ℝ) 1,
      betaStar ≤ aT ye * ∫ x in (0 : ℝ)..1,
        (Real.exp (-(x * (2 - ye))) + x * Real.exp (-(x * (2 - ye)))) ^ 2) ∧
    aT 0 * (∫ x in (0 : ℝ)..1,
        (Real.exp (-(x * (2 - 0))) + x * Real.exp (-(x * (2 - 0)))) ^ 2) = betaStar := by sorry

end OfflineStochMatch.Attenuation
