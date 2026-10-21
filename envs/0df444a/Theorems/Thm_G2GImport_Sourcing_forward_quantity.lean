-- Prove2me | Theorems.Thm_G2GImport_Sourcing_forward_quantity
-- name    : G2GImport.Sourcing.forward_quantity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:49.261428+00:00
-- url     : https://prove2.me/theorems/ae9162bb-39a4-40ce-9aef-b7d50aa570eb
-- title:
--   Proposition 2: symmetric all-forward quantity
-- statement:
--   Suppose $l\ge1$ identical suppliers negotiate forward contracts, with no ad hoc suppliers. Under the paper's positive-production assumptions, each supplier's contracted purchase quantity in every symmetric Nash-in-Nash equilibrium is
--   $$q^{f*}=k^{f*}=\frac{1-\sqrt c}{l}.$$
--   Forward suppliers produce their contracted quantities, so the buyer's aggregate forward purchase is $1-\sqrt c$. This is the pure all-forward case of Proposition 2.
--
--   **Formalization Note** Production equal to the contract is the explicit assumption of §4.1.
-- source:
--   Mu, Hu, Reddy & Gavirneni, Negotiating government-to-government food importing contracts: a Nash bargaining framework, accepted manuscript (MSOM, doi:10.1287/msom.2021.1027), PDF p. 8, Proposition 2, first bullet; PDF p. 14, proof

import Mathlib
import Definitions.Def_G2GImport_Sourcing_Model

namespace G2GImport.Sourcing

/-- Proposition 2, first bullet: the pure all-forward symmetric quantity. -/
theorem forward_quantity (P : Params) (hS : P.Standing)
    (l : ℕ) (hl : 1 ≤ l) (q t : ℝ)
    (heq : IsForwardEq P l q t) :
    q = (1 - Real.sqrt P.c) / (l : ℝ) := by sorry

end G2GImport.Sourcing
