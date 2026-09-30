-- Prove2me | Theorems.Thm_InventoryControl_rq_fill_rate_batch
-- name    : InventoryControl.rq_fill_rate_batch
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:45:56.082628+00:00
-- url     : https://prove2.me/theorems/30438f82-4031-40c5-98e9-dc746e6db82a
-- title:
--   Eq. (5.54): $S_2 = S_3 = 1 - \mathbb{E}(B)/Q$ agrees with Eq. (5.52)
-- statement:
--   The fill rate computed batch by batch coincides with the fill rate computed from the inventory
--   level distribution. Under a continuous review $(R,Q)$ policy with $Q > 0$ and normal lead-time
--   demand ($\sigma' > 0$), with $\mathbb{E}(B)$ the expected backordered quantity covered by one
--   batch,
--
--   $$ 1 - \frac{\mathbb{E}(B)}{Q} \;=\; \Pr[IL > 0] . $$
--
--   The left-hand side is Eq. (5.54), the fill rate as one minus the fraction of each batch that
--   goes to backorders; the right-hand side is the ready rate $S_3 = 1 - F(0)$ of Sect. 5.7.2. The
--   book presents the batch argument precisely to show that the two standard techniques of
--   inventory theory, following the inventory level and following an individual batch, agree.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, pp. 82-83, Sect. 5.8, Eq. (5.54) and the sentence after Eq. (5.55): 'Combining (5.54) and (5.55) we obtain (5.52)'

import Definitions.Def_InventoryControl_rq

namespace InventoryControl

theorem rq_fill_rate_batch (R Q m s : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    1 - rqBatchBackorders R Q m s / Q = rqReadyRate R Q m s := by sorry

end InventoryControl
