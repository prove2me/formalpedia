-- Prove2me | Theorems.Thm_LossAverseAuction_CPERevenue_proposition_9
-- name    : LossAverseAuction.CPERevenue.proposition_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:27.720472+00:00
-- url     : https://prove2.me/theorems/56ae54d5-25fb-407a-854d-1a83787aa7a3
-- title:
--   Proposition 9, p. 11 — SPA equilibrium bidding formula
-- statement:
--   Under Assumption 1 there exists a symmetric increasing SPA CPE strategy, and every such strategy satisfies the following formula. Put $A_1(t)=f_1(t)V(t,t)+F_1(t)V_1(t,t)-\Psi_1(t,t)-\Omega_1(t,t)$. For $t\in(\underline t,\overline t]$,
--
--   $$\beta_{II}(t)=\frac{A_1(t)}{(1+\Lambda^m)f_1(t)}+\frac{2\Lambda^m}{(1+\Lambda^m)^2}\int_{\underline t}^{t}A_1(s)e^{2\Lambda^m[F_1(t)-F_1(s)]/(1+\Lambda^m)}\,ds.$$
--
--   This gives both existence and the bidding formula for every symmetric increasing SPA CPE.
--
--   **Formalization Note** The lower endpoint is excluded because f1 there may vanish.
-- source:
--   Balzer & Rosato, Expectations-Based Loss Aversion in Auctions with Interdependent Values, Management Science (Articles in Advance, 2020; doi:10.1287/mnsc.2019.3563), §4.2, Proposition 9 and eq. (13), p. 11 (PDF 12); proof p. 16 (PDF 17)

import Mathlib
import Definitions.Def_LossAverseAuction_CPERevenue_Model

namespace LossAverseAuction.CPERevenue

open MeasureTheory

theorem proposition_9 {m : ℕ} (E : Env m) (hS : E.Standing)
    (hA1 : E.Assumption1) :
    (∃ β : ℝ → ℝ, E.IsSymCPE .SPA β ∧
      ∀ t ∈ Set.Ioc E.tl E.th,
        β t = E.A1 t / ((1 + E.Lm) * E.f1 t) +
          (2 * E.Lm / (1 + E.Lm) ^ 2) *
            ∫ s in E.tl..t,
              E.A1 s * Real.exp (2 * E.Lm * (E.F1 t - E.F1 s) / (1 + E.Lm))) ∧
    ∀ β : ℝ → ℝ, E.IsSymCPE .SPA β →
      ∀ t ∈ Set.Ioc E.tl E.th,
        β t = E.A1 t / ((1 + E.Lm) * E.f1 t) +
          (2 * E.Lm / (1 + E.Lm) ^ 2) *
            ∫ s in E.tl..t,
              E.A1 s * Real.exp (2 * E.Lm * (E.F1 t - E.F1 s) / (1 + E.Lm)) := by sorry
end LossAverseAuction.CPERevenue
