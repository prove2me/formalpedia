-- Prove2me | Theorems.Thm_Multihoming_Thresholds_profit_threshold
-- name    : Multihoming.Thresholds.profit_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:36.333138+00:00
-- url     : https://prove2.me/theorems/45251d05-aa1c-45a6-81e9-7c13bbb93093
-- title:
--   Appendix A1, PDF p. 27 (printed p. 21) — π^M(μ) > π^M(0) if e < e_π, and π^M(μ) < π^M(0) if e > e_π
-- statement:
--   Let $t>0$, $0<\mu<t$ and $e\ge 0$. Let $\pi^M(\mu)$ be the symmetric profit (price (26) times demand (14) at symmetric prices), so that $\pi^M(0)=e^2/(4t)$, and let
--   $$e_\pi\equiv\frac{4t^2(t-\mu)+2t(2t-\mu)\sqrt{t^2-\mu^2}}{4t^2-3t\mu+\mu^2}.$$
--   Then
--
--   1. if $e<e_\pi$, then $\pi^M(\mu)>\pi^M(\mu=0)$;
--   2. if $e>e_\pi$, then $\pi^M(\mu)<\pi^M(\mu=0)$.
--
--   This is the profit half of Proposition 2.
--
--   **Formalization Note** The paper's display gives item 1. Item 2 is the converse half the proposition asserts; it holds because $\pi^M(\mu)-\pi^M(0)$ is a quadratic in $e$ with negative leading coefficient $-\mu(4t^2-3t\mu+\mu^2)$ (up to a positive factor) whose positive root is $e_\pi$. The hypothesis $e\ge 0$ (exclusive features are a nonnegative value) is added: the quadratic also has a negative root, below which item 1 fails.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 27 (printed p. 21), Appendix A1, opening display

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model

namespace Multihoming.Thresholds

theorem profit_threshold (t μ e : ℝ) (ht : 0 < t) (hμ : 0 < μ) (hμt : μ < t) (he : 0 ≤ e) :
    (e < ePi t μ → piM t 0 e < piM t μ e) ∧
    (ePi t μ < e → piM t μ e < piM t 0 e) := by sorry

end Multihoming.Thresholds
