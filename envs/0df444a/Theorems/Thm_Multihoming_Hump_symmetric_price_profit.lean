-- Prove2me | Theorems.Thm_Multihoming_Hump_symmetric_price_profit
-- name    : Multihoming.Hump.symmetric_price_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:33.716984+00:00
-- url     : https://prove2.me/theorems/ee3f351b-7de8-4594-8980-c69bc408e9f8
-- title:
--   (25)–(26), PDF p. 20 (printed p. 14) — pᴹ is a fixed point of (15), demand is (25), and πᴹ = pᴹxᴹ
-- statement:
--   Let $t>0$, $0\le\mu<t$ and $e\in\mathbb R$. With symmetric firms, the price $p^M=(t-\mu)(\mu+e)/(2t-\mu)$ of (26) satisfies:
--
--   1. it is a fixed point of the reaction function (15): $p_i^M(p^M)=p^M$;
--   2. the multihoming demand (14) at the price pair $(p^M,p^M)$ is (25):
--   $$x_i^M(p^M,p^M)=t\,\frac{\mu+e}{(2t-\mu)(t+\mu)};$$
--   3. the profit (26) equals price times demand: $\pi^M=p^M\,x_i^M(p^M,p^M)$.
--
--   This ties the closed forms (26), which Proposition 3 studies, to the model's demand and reaction function.
--
--   **Formalization Note** The identities hold for every real $e$; partial multihoming is not needed for them. The domain is $\mu<t$ because (14) is undefined at $\mu=t$.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 20 (printed p. 14), (25)–(26)

import Mathlib
import Definitions.Def_Multihoming_Hump_Model

namespace Multihoming.Hump

/-- (25)–(26), PDF p. 20: for 0 ≤ μ < t, the price pᴹ is a fixed point of the reaction
function (15), the demand (14) at (pᴹ, pᴹ) is (25), and πᴹ = pᴹ · xᴹ. -/
theorem symmetric_price_profit (t μ e : ℝ) (ht : 0 < t) (hμ0 : 0 ≤ μ) (hμt : μ < t) :
    Multihoming.Thresholds.reactM t μ e (Multihoming.Thresholds.pM t μ e) = Multihoming.Thresholds.pM t μ e ∧
    Multihoming.Thresholds.demandM t μ e (Multihoming.Thresholds.pM t μ e) (Multihoming.Thresholds.pM t μ e) = t * (μ + e) / ((2 * t - μ) * (t + μ)) ∧
    piM t μ e = Multihoming.Thresholds.pM t μ e * Multihoming.Thresholds.demandM t μ e (Multihoming.Thresholds.pM t μ e) (Multihoming.Thresholds.pM t μ e) := by sorry

end Multihoming.Hump
