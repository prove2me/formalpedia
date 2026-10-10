-- Prove2me | Theorems.Thm_GreshamLaw_thiers_law
-- name    : GreshamLaw.thiers_law
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:52.766974+00:00
-- url     : https://prove2.me/theorems/cdc9e3bb-9b31-49bb-94ea-63751b78bec1
-- title:
--   Thiers' law: without legal tender, nearly worthless money is refused
-- statement:
--   Suppose there is no legal tender law, so a seller accepts a set $P$ of coins for a good of price $p>0$ only if the total melt value of $P$ is at least $p$. Let the wallet $s$ consist of good coins and bad coins, and suppose the bad coins are nearly worthless: each has melt value at most $\varepsilon$, with
--
--   $$|\text{bad}|\cdot\varepsilon<p .$$
--
--   Then every payment $P\subseteq s$ that the seller accepts contains at least one good coin.
--
--   This is the reverse of Gresham's law ("Thiers' law"): in the absence of effective legal tender laws the seller will not accept anything but money of certain value.
-- source:
--   Wikipedia, "Gresham's law" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Gresham%27s_law

import Mathlib
import Definitions.Def_GreshamLaw_Model

namespace GreshamLaw

theorem thiers_law {ι : Type*} [DecidableEq ι] (coin : ι → Coin) (s good bad : Finset ι)
    (hpart : good ∪ bad = s) (p ε : ℝ) (hp : 0 < p)
    (hworthless : ∀ b ∈ bad, (coin b).melt ≤ ε) (hsmall : (bad.card : ℝ) * ε < p)
    (P : Finset ι) (hPs : P ⊆ s) (hacc : AcceptsAtMarketValue coin P p) :
    (P ∩ good).Nonempty := by sorry

end GreshamLaw
