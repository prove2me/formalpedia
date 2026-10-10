-- Prove2me | Theorems.Thm_GreshamLaw_newton_guinea_arbitrage
-- name    : GreshamLaw.newton_guinea_arbitrage
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:58.731208+00:00
-- url     : https://prove2.me/theorems/8ba6229a-301e-40fc-8b4a-93f8eb2a9525
-- title:
--   Newton's guinea: overvalued gold makes silver-for-gold arbitrage profitable without bound
-- statement:
--   Let the legal rate at home be $r$ silver shillings per gold guinea, and suppose that abroad the gold of one guinea costs the silver of $m$ shillings, with
--
--   $$0<m<r$$
--
--   (gold is overvalued at home, as after Newton fixed the guinea at 21 shillings in 1717). Starting from $N>0$ shillings, one round of shipping silver abroad, buying gold, coining guineas at home and buying shillings at the legal rate yields $A_{r,m}(N)=\tfrac{N}{m}r$ shillings. Then
--
--   1. one round is strictly profitable: $N<A_{r,m}(N)$;
--   2. repeating the round makes the holding grow without bound: $A_{r,m}^{\,n}(N)\to\infty$ as $n\to\infty$.
--
--   This is the mechanism by which good silver coin left Britain and Britain moved onto a de facto gold standard.
--
--   **Formalization Note** Transport and minting costs are ignored.
-- source:
--   Wikipedia, "Gresham's law" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Gresham%27s_law

import Mathlib
import Definitions.Def_GreshamLaw_Model

namespace GreshamLaw

theorem newton_guinea_arbitrage (r m N : ℝ) (hm : 0 < m) (hmr : m < r) (hN : 0 < N) :
    N < arbitrageRound r m N ∧
      Filter.Tendsto (fun n : ℕ => (arbitrageRound r m)^[n] N) Filter.atTop Filter.atTop := by sorry

end GreshamLaw
