-- Prove2me | Theorems.Thm_NewsBundling_Unilateral_eq2_publisher_profit
-- name    : NewsBundling.Unilateral.eq2_publisher_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:54.480744+00:00
-- url     : https://prove2.me/theorems/c86783f7-9873-4e91-9754-4e3d52924aac
-- title:
--   Display (2), p. 11 — publisher’s piecewise profit
-- statement:
--   Under Table 1's assumptions, fix any subgame-perfect equilibrium strategy profile $\sigma$. At every feasible quality $q\in[0,1]$, the publisher's profit from choosing $q$ against the continuation strategies is
--
--   $$\pi_1(q)=\begin{cases}\phi_1q-\dfrac{cq^2}{2},&q\le\Lambda,\\[4pt]\dfrac{\phi_1\Lambda(1-q)}{1-\Lambda}+\dfrac{\beta(q-\Lambda)}{1-\Lambda}-\dfrac{cq^2}{2},&q>\Lambda.\end{cases}$$
--
--   This is the first-stage objective whose maximizers yield the equilibrium qualities. The formula includes $q=1$, where the publisher receives all attention regardless of the platform's indifferent share.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), p. 11, display (2)

import Mathlib
import Definitions.Def_NewsBundling_Unilateral_Setting

namespace NewsBundling.Unilateral

/-- Equation (2), p. 11: publisher profit for every feasible quality. -/
theorem eq2_publisher_profit (β φ0 φ1 c Λ : ℝ)
    (h : StandingAssumptions β φ0 φ1 c Λ) :
    ∀ σ, IsSPE β φ0 φ1 c Λ σ →
      ∀ q ∈ Set.Icc (0 : ℝ) 1,
        publisherProfit β φ1 c σ q =
          if q ≤ Λ then φ1 * q - c * q ^ 2 / 2
          else φ1 * Λ * (1 - q) / (1 - Λ) +
            β * (q - Λ) / (1 - Λ) - c * q ^ 2 / 2 := by sorry

end NewsBundling.Unilateral
