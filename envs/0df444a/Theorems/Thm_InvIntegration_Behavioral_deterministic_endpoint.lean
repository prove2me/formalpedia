-- Prove2me | Theorems.Thm_InvIntegration_Behavioral_deterministic_endpoint
-- name    : InvIntegration.Behavioral.deterministic_endpoint
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:04.69386+00:00
-- url     : https://prove2.me/theorems/ef40bca1-db34-46a7-b69d-c2d3c7d5b126
-- title:
--   Proof of Proposition 5, EC p. 5 (PDF 37) — with deterministic demand ξ2 = 0 and v∗ = p
-- statement:
--   Let the market demand be deterministic, equal to $m>0$ (the normal law with standard deviation $0$). Then every equilibrium $(q,v,\xi)$ has
--   $$\xi = 0 \quad\text{and}\quad v = p.$$
--
--   The proof of Proposition 5 uses this at the endpoints $\rho=-1$ (where the integrated demand $D_1+D_2$ is deterministic) and $\sigma=0$, where $v^*_m(0)=v^*_I(0)=p$.
--
--   **Formalization Note.** The endpoints lie outside the model's domain ($\rho\in(-1,1)$, $\sigma>0$); the statement is about the Dirac demand law.
-- source:
--   Aflaki & Swinney, Inventory Integration with Rational Consumers, SSRN preprint 2842182 (July 2020), EC p. 5 (PDF 37), proof of Proposition 5, parts (ii)–(iii)

import Mathlib
import Definitions.Def_InvIntegration_Behavioral_Model

namespace InvIntegration.Behavioral

theorem deterministic_endpoint (P : Params) (hS : P.Standing) (m : ℝ) (hm : 0 < m)
    (q v ξ : ℝ) (hE : IsEquilibrium P m 0 q v ξ) :
    ξ = 0 ∧ v = P.p := by sorry

end InvIntegration.Behavioral
