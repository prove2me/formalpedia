-- Prove2me | Theorems.Thm_G2GImport_Sourcing_ad_hoc_production
-- name    : G2GImport.Sourcing.ad_hoc_production
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:48.209389+00:00
-- url     : https://prove2.me/theorems/5b4d2ea3-b336-47f5-9b2f-3c6050df1e7d
-- title:
--   Proposition 2: symmetric all-ad-hoc production
-- statement:
--   Suppose $l\ge1$ identical suppliers participate only in ad hoc negotiations, with unit production cost $c$ and buyer bargaining power $\gamma$, where $0<\gamma<1$ and $0<c<1-\gamma$. In every symmetric equilibrium each supplier's pre-yield production quantity is
--   $$k^{a*}=\frac{1-\sqrt{c/(1-\gamma)}}{l}.$$
--   The formula is the pure ad hoc case of Proposition 2 and the symmetric specialization of equation (A.4). It fixes total ad hoc production independently of the number of suppliers.
--
--   **Formalization Note** The strict cost bound selects the positive-production branch of (A.4).
-- source:
--   Mu, Hu, Reddy & Gavirneni, Negotiating government-to-government food importing contracts: a Nash bargaining framework, accepted manuscript (MSOM, doi:10.1287/msom.2021.1027), PDF p. 8, Proposition 2, second bullet; PDF p. 14, equation (A.4)

import Mathlib
import Definitions.Def_G2GImport_Sourcing_Model

namespace G2GImport.Sourcing

/-- Proposition 2, second bullet: the pure all-ad-hoc case of (A.4). -/
theorem ad_hoc_production (P : Params) (hS : P.Standing)
    (l : ℕ) (hl : 1 ≤ l) (k : ℝ) (q t : ℝ → ℝ)
    (heq : IsAdHocEq P l k q t) :
    k = (1 - Real.sqrt (P.c / (1 - P.γ))) / (l : ℝ) := by sorry

end G2GImport.Sourcing
