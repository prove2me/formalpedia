-- Prove2me | Theorems.Thm_GreshamLaw_optimal_payment_iff_exchange
-- name    : GreshamLaw.optimal_payment_iff_exchange
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:40.826593+00:00
-- url     : https://prove2.me/theorems/4088c5fd-3268-40af-98c0-55213c41f6de
-- title:
--   Optimal payments: every paid coin is worth no more than every retained coin
-- statement:
--   Let $s$ be a finite wallet of coins, all of the same positive face value. For a debt $d$ and a set $P$ of coins, $P$ is an optimal payment of $d$ from $s$ if and only if
--
--   1. $P$ is a legal payment of $d$ ($P\subseteq s$ and the face values of $P$ add up to $d$), and
--   2. every paid coin is intrinsically worth at most every retained coin:
--   $$m_i\le m_j\qquad\text{for all } i\in P,\ j\in s\setminus P .$$
--
--   Under legal tender at equal value, a payer who keeps the more valuable money therefore always pays with the intrinsically least valuable coins available.
-- source:
--   Wikipedia, "Gresham's law" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Gresham%27s_law

import Mathlib
import Definitions.Def_GreshamLaw_Model

namespace GreshamLaw

theorem optimal_payment_iff_exchange {ι : Type*} [DecidableEq ι] (coin : ι → Coin)
    (s P : Finset ι) (d : ℝ)
    (hlegal : EqualLegalTender coin s) (hpos : ∀ i ∈ s, 0 < (coin i).face) :
    IsOptimalPayment coin s P d ↔
      IsLegalPayment coin s P d ∧ ∀ i ∈ P, ∀ j ∈ s \ P, (coin i).melt ≤ (coin j).melt := by sorry

end GreshamLaw
