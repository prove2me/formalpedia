-- Prove2me | Theorems.Thm_Multihoming_Local_price_fixed_point
-- name    : Multihoming.Local.price_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:23.039986+00:00
-- url     : https://prove2.me/theorems/c3c4cda9-a224-4bf7-8a90-f1dbf0dbfc5e
-- title:
--   (16), PDF p. 18 (printed p. 12) — the candidate prices solve both reaction functions (15) simultaneously
-- statement:
--   Let $t>0$ and $0\le\mu<t$. The candidate partial-multihoming prices of (16),
--
--   $$
--   p_i^M=\frac{t-\mu}{2t-\mu}(\mu+e_i)+\frac{\mu t}{4t^2-\mu^2}(e_i-e_j),\qquad
--   p_j^M=\frac{t-\mu}{2t-\mu}(\mu+e_j)+\frac{\mu t}{4t^2-\mu^2}(e_j-e_i),
--   $$
--
--   solve the two reaction functions (15) simultaneously:
--
--   $$
--   p_i^M=p_i^M(p_j^M)\quad\text{and}\quad p_j^M=p_j^M(p_i^M).
--   $$
--
--   Together with (15), this identifies (16) as the pair of mutual best responses under the multihoming demand.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 18 (printed p. 12), (16)

import Mathlib
import Definitions.Def_Multihoming_Local_Model

namespace Multihoming.Local

/-- (16), PDF p. 18: the candidate prices (16) of the two firms solve the two reaction
functions (15) simultaneously. -/
theorem price_fixed_point (t μ ei ej : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) :
    priceM t μ ei ej = reactM t μ ei ej (priceM t μ ej ei) ∧
      priceM t μ ej ei = reactM t μ ej ei (priceM t μ ei ej) := by sorry

end Multihoming.Local
