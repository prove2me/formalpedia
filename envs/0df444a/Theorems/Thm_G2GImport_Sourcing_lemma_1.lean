-- Prove2me | Theorems.Thm_G2GImport_Sourcing_lemma_1
-- name    : G2GImport.Sourcing.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:49.810829+00:00
-- url     : https://prove2.me/theorems/927c5820-a706-4f60-bec4-46c094f8a842
-- title:
--   Lemma 1: single-supplier ad hoc production, trade, and payoffs
-- statement:
--   For one ad hoc supplier with cost $c$ and buyer bargaining power $\gamma$ in the positive-production regime, write $s=\sqrt{c/(1-\gamma)}$. Every equilibrium has production $k^{a*}=1-s$, expected purchase $\mathbb E[q^a(Y)]=(1-c/(1-\gamma))/2$, and expected payment $\mathbb E[t^a(Y)]=(1-cs-\gamma)/3$. The buyer's expected net utility and the supplier's expected profit are
--   $$U_B^{a*}=\frac{2-c\gamma s-\gamma-\gamma^2}{3(1-\gamma)},\qquad U_S^{a*}=\frac{c(2s-3)+1-\gamma}{3}.$$
--   This is the single-supplier benchmark for the multiple-sourcing analysis.
--
--   **Formalization Note** The theorem describes every equilibrium of the paper's Nash bargaining model, with $0<c<1-\gamma$ to exclude the zero-production boundary.
-- source:
--   Mu, Hu, Reddy & Gavirneni, Negotiating government-to-government food importing contracts: a Nash bargaining framework, accepted manuscript (MSOM, doi:10.1287/msom.2021.1027), PDF p. 5, Lemma 1

import Mathlib
import Definitions.Def_G2GImport_Sourcing_Model

namespace G2GImport.Sourcing

/-- Lemma 1: the single-supplier ad hoc quantities, payment, and payoffs. -/
theorem lemma_1 (P : Params) (hS : P.Standing) (k : ℝ) (q t : ℝ → ℝ)
    (heq : IsAdHocEq P 1 k q t) :
    k = 1 - Real.sqrt (P.c / (1 - P.γ)) ∧
    EY q = (1 - P.c / (1 - P.γ)) / 2 ∧
    EY t = (1 - P.c * Real.sqrt (P.c / (1 - P.γ)) - P.γ) / 3 ∧
    adHocBuyer 1 q t =
      (2 - P.c * P.γ * Real.sqrt (P.c / (1 - P.γ)) - P.γ - P.γ ^ 2) /
        (3 * (1 - P.γ)) ∧
    adHocSupplier P k t =
      (P.c * (2 * Real.sqrt (P.c / (1 - P.γ)) - 3) + 1 - P.γ) / 3 := by sorry

end G2GImport.Sourcing
