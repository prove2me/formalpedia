-- Prove2me | Theorems.Thm_InventoryControl_rq_batch_backorders
-- name    : InventoryControl.rq_batch_backorders
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:45:20.943082+00:00
-- url     : https://prove2.me/theorems/7728c53a-2f79-4094-a245-caf4644a0f23
-- title:
--   Eq. (5.55): $\mathbb{E}(B) = \sigma' G\left(\frac{R-\mu'}{\sigma'}\right) - \sigma' G\left(\frac{R+Q-\mu'}{\sigma'}\right)$
-- statement:
--   Section 5.8 follows a single batch of $Q$ units, ordered when the inventory position is $R$,
--   and asks how much of the demand it will cover has already been backordered when it arrives.
--   With lead-time demand $u$ this backordered quantity is $B = 0$ if $u \le R$, $B = u - R$ if
--   $R < u \le R + Q$, and $B = Q$ if $u > R + Q$, that is $B = \min\{(u - R)^{+}, Q\}$. For
--   normal lead-time demand with mean $\mu'$ and standard deviation $\sigma' > 0$,
--
--   $$ \mathbb{E}(B) \;=\; \sigma'\,G\!\left(\frac{R - \mu'}{\sigma'}\right) - \sigma'\,G\!\left(\frac{R + Q - \mu'}{\sigma'}\right), $$
--
--   for every $Q \ge 0$ and every reorder point $R$, negative reorder points included.
--
--   The derivation splits the expectation at $R$ and $R + Q$ and recognizes each piece as a loss
--   function. It is the second route to the fill rate: combined with Eq. (5.54), $S_2 = 1 -
--   \mathbb{E}(B)/Q$, it reproduces Eq. (5.52) without passing through the inventory level
--   distribution, and the book notes that the argument covers negative $R$ as well.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 83, Sect. 5.8, Eq. (5.55)

import Definitions.Def_InventoryControl_rq

namespace InventoryControl

theorem rq_batch_backorders (R Q m s : ℝ) (hQ : 0 ≤ Q) (hs : 0 < s) :
    rqBatchBackorders R Q m s
      = s * normalLoss ((R - m) / s) - s * normalLoss ((R + Q - m) / s) := by sorry

end InventoryControl
