-- Prove2me | Theorems.Thm_MyersonAuction_Optimal_optimal_auction_theorem
-- name    : MyersonAuction.Optimal.optimal_auction_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:59:51.462073+00:00
-- url     : https://prove2.me/theorems/41835a77-1aa7-44f3-af3e-27398145a10d
-- title:
--   Theorem — Myerson’s ironed allocation and envelope payments are optimal
-- statement:
--   Let $\bar c_i$ be the ironed priority of bidder $i$ and let $M(t)$ contain those bidders whose priority is maximal and at least the seller’s value $t_0$. Allocate the object equally among the members of $M(t)$ and charge the payments
--
--   $$
--   \bar p_i(t)=\begin{cases}|M(t)|^{-1},&i\in M(t),\\0,&i\notin M(t),\end{cases}
--   \qquad
--   \bar x_i(t)=\bar p_i(t)v_i(t)-\int_{a_i}^{t_i}\bar p_i(t_{-i},s)\,ds.
--   $$
--
--   Then $(\bar p,\bar x)$ is feasible and maximizes the seller’s expected utility among all feasible direct mechanisms. This is Myerson’s general-case optimal auction theorem.
--
--   **Formalization Note** The bidder set is finite and nonempty; supports may differ and may include negative values. The definition of $g_i(1)$ uses the left derivative, preserving the boundary priority.
-- source:
--   Myerson, Optimal Auction Design, Math. Oper. Res. 6(1) (1981), p. 69, §6, Theorem, eqs. (6.7)–(6.8)

import Definitions.Def_MyersonAuction_Optimal_Ironing

noncomputable section

namespace MyersonAuction.Optimal

theorem optimal_auction_theorem {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : Environment ι) : IsOptimal E (pbar E) (xbar E) := by sorry

end MyersonAuction.Optimal
