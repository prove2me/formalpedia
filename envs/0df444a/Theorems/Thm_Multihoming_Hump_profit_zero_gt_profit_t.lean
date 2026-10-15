-- Prove2me | Theorems.Thm_Multihoming_Hump_profit_zero_gt_profit_t
-- name    : Multihoming.Hump.profit_zero_gt_profit_t
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:31.538147+00:00
-- url     : https://prove2.me/theorems/16cf8ddc-6cad-45f0-8c25-b9faa27f9687
-- title:
--   Appendix A1, PDF pp. 28–29 (printed pp. 22–23) — πᴹ(μ = 0) > πᴹ(μ = t)
-- statement:
--   Let $t>0$ and $e>0$, and let $\pi^M(\mu)=t(t-\mu)(e+\mu)^2/((t+\mu)(2t-\mu)^2)$ be the symmetric profit (26). Then
--   $$\pi^M(\mu=0)>\pi^M(\mu=t).$$
--
--   Maximized profits are thus larger without network effects than with network effects that are strong enough.
--
--   **Formalization Note** $\pi^M(t)=0$ and $\pi^M(0)=e^2/(4t)$, so the statement needs $e>0$, which is added: at $e=0$ both values are $0$.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF pp. 28–29 (printed pp. 22–23), Appendix A1, sentence "It is also immediately clear from (26) …"

import Mathlib
import Definitions.Def_Multihoming_Hump_Model

namespace Multihoming.Hump

/-- Appendix A1, PDF pp. 28–29: πᴹ(μ = 0) > πᴹ(μ = t) (for e > 0). -/
theorem profit_zero_gt_profit_t (t e : ℝ) (ht : 0 < t) (he0 : 0 < e) :
    piM t t e < piM t 0 e := by sorry

end Multihoming.Hump
