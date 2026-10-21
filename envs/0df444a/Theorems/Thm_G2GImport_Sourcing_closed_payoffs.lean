-- Prove2me | Theorems.Thm_G2GImport_Sourcing_closed_payoffs
-- name    : G2GImport.Sourcing.closed_payoffs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:33.646891+00:00
-- url     : https://prove2.me/theorems/4f3437e7-5851-427b-9690-2a9d8a24d4d3
-- title:
--   Proposition 3 proof: four symmetric equilibrium payoff formulas
-- statement:
--   Let $l\ge1$ and consider the two pure, symmetric sourcing games with common supplier cost $c$ and buyer bargaining power $\gamma$. The buyer's expected net utility and each supplier's expected profit in every all-ad-hoc equilibrium equal the paper's closed forms $U_B^{a*}(l)$ and $U_S^{a*}(l)$. In every all-forward equilibrium they equal $U_B^{f*}(l)$ and $U_S^{f*}(l):$
--   $$\bigl(U_B^a,U_S^a,U_B^f,U_S^f\bigr)=\bigl(U_B^{a*}(l),U_S^{a*}(l),U_B^{f*}(l),U_S^{f*}(l)\bigr).$$
--   All four expressions are defined separately from equilibrium payoffs, with their exact constants in the source code, so these identities connect the model to the formulas used in the proof of Proposition 3.
--
--   **Formalization Note** The printed $n$ in $U_S^{f*}$ is read as $l$, the forward supplier count in this pure regime.
-- source:
--   Mu, Hu, Reddy & Gavirneni, Negotiating government-to-government food importing contracts: a Nash bargaining framework, accepted manuscript (MSOM, doi:10.1287/msom.2021.1027), PDF p. 14, proof of Proposition 3, four displayed payoff formulas

import Mathlib
import Definitions.Def_G2GImport_Sourcing_ClosedForms

namespace G2GImport.Sourcing

/-- The four payoff formulas in the proof of Proposition 3. -/
theorem closed_payoffs (P : Params) (hS : P.Standing)
    (l : ℕ) (hl : 1 ≤ l) :
    (∀ k q t, IsAdHocEq P l k q t →
      adHocBuyer l q t = adHocBuyerClosed P (l : ℝ) ∧
      adHocSupplier P k t = adHocSupplierClosed P (l : ℝ)) ∧
    (∀ q t, IsForwardEq P l q t →
      fwdBuyer l q t = fwdBuyerClosed P (l : ℝ) ∧
      fwdSupplier P q t = fwdSupplierClosed P (l : ℝ)) := by sorry

end G2GImport.Sourcing
