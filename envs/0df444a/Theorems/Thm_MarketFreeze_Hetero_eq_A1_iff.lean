-- Prove2me | Theorems.Thm_MarketFreeze_Hetero_eq_A1_iff
-- name    : MarketFreeze.Hetero.eq_A1_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:42.999979+00:00
-- url     : https://prove2.me/theorems/efada9c8-cf71-4aef-8a57-ab36c558bd4a
-- title:
--   (A1), proof of Proposition 1, p. 34 — (A1) holds iff ∆π^hom(0) > 0 and ∆π^hom(θ̄) < 0
-- statement:
--   Under the standing restrictions and Assumption 1, the intermediate-cost condition (A1),
--   $$\frac{0.5(1-\bar\theta)X}{1+2\psi(1-\bar\theta)^{-1}}-\bar\theta(X-I)+0.5(1-\bar\theta)Y(\bar\theta)<c<\frac{0.5X}{1+2\psi}+0.5\,Y(0),$$
--   holds if and only if the value added of screening is positive at $\theta=0$ and negative at $\theta=\bar\theta$:
--   $$\Delta\pi^{hom}(0)>0\quad\text{and}\quad\Delta\pi^{hom}(\bar\theta)<0.$$
--   This is how the proof of Proposition 1 translates the two endpoint signs into a condition on the screening cost $c$.
--
--   **Formalization Note** Pure algebra; Assumption 1 is used only to know $X>I$, hence $\bar\theta<1$.
-- source:
--   Song & Thakor, Market Freeze and Bank Capital Structure Heterogeneity, SSRN 3667175 (version of 2022-02-21; forthcoming Management Science, doi:10.1287/mnsc.2022.4374), proof of Proposition 1 (Appendix A), (A1), p. 34

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

namespace MarketFreeze.Hetero

theorem eq_A1_iff (P : Params) (h0 : Standing P) (h1 : Assumption1 P) :
    CondA1 P ↔ 0 < dPi P 0 ∧ dPi P P.θbar < 0 := by sorry

end MarketFreeze.Hetero
