-- Prove2me | Theorems.Thm_InventoryControl_rq_mean_level
-- name    : InventoryControl.rq_mean_level
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:46:56.391533+00:00
-- url     : https://prove2.me/theorems/24f065b4-f2f7-4190-a399-a3bc08073bd2
-- title:
--   The average inventory level is $R + Q/2 - \mu'$
-- statement:
--   Under a continuous review $(R,Q)$ policy with $Q > 0$ and normal lead-time demand with mean
--   $\mu'$ and standard deviation $\sigma' > 0$, the expected inventory level is
--
--   $$ \mathbb{E}(IL) \;=\; R + \frac{Q}{2} - \mu' . $$
--
--   It is the difference between the average inventory position, $R + Q/2$ for a position uniform
--   on $[R, R+Q]$, and the average lead-time demand. The identity supplies the first term of the
--   cost expression (5.62), $h\,\mathbb{E}(IL)$, and it is why the safety stock $SS = R - \mu'$ of
--   Eq. (5.46) is read as the average stock on hand just before a batch arrives.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 85, Sect. 5.9.2, Eq. (5.62) and the sentence after it: 'In the first line of (5.62) we use that the average inventory position is R + Q/2 in the continuous case'

import Definitions.Def_InventoryControl_rq

namespace InventoryControl

theorem rq_mean_level (R Q m s : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    ∫ x, x ∂(rqLevel R Q m s) = R + Q / 2 - m := by sorry

end InventoryControl
