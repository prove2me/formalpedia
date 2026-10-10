-- Prove2me | Theorems.Thm_GreshamLaw_gresham_law
-- name    : GreshamLaw.gresham_law
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:24.63724+00:00
-- url     : https://prove2.me/theorems/40dbcbb4-01c0-40db-bafe-b258bbe31c63
-- title:
--   Gresham's law: under equal legal tender, bad money is spent before good
-- statement:
--   Let a finite wallet $s$ be made up of good coins and bad coins, all carrying the same face value (legal tender at equal value), and suppose every bad coin has strictly smaller melt value than every good coin:
--
--   $$m_b<m_g\qquad\text{for all bad } b \text{ and good } g .$$
--
--   Let $P$ be an optimal payment of some debt $d$ from $s$, i.e. a legal payment after which the payer retains as much intrinsic value as any other legal payment of $d$ would allow. Then
--
--   $$P\cap\text{good}\neq\varnothing\;\Longrightarrow\;\text{bad}\subseteq P .$$
--
--   A good coin is handed over only once every bad coin has been handed over: as long as the payer still holds a bad coin, only bad coins circulate and good coins are kept. This is the article's statement that a currency of good and bad money, both required to be accepted at equal value, becomes dominated by the bad money.
-- source:
--   Wikipedia, "Gresham's law" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Gresham%27s_law

import Mathlib
import Definitions.Def_GreshamLaw_Model

namespace GreshamLaw

theorem gresham_law {ι : Type*} [DecidableEq ι] (coin : ι → Coin) (s good bad : Finset ι)
    (hpart : good ∪ bad = s)
    (hlegal : EqualLegalTender coin s)
    (hworse : ∀ g ∈ good, ∀ b ∈ bad, (coin b).melt < (coin g).melt)
    (d : ℝ) (P : Finset ι) (hP : IsOptimalPayment coin s P d) :
    (P ∩ good).Nonempty → bad ⊆ P := by sorry

end GreshamLaw
