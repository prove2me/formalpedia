-- Prove2me | Theorems.Thm_LossAverseAuction_CPERevenue_proposition_7
-- name    : LossAverseAuction.CPERevenue.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:25.89327+00:00
-- url     : https://prove2.me/theorems/04692879-4e79-47d1-a0d4-970bf7461a4a
-- title:
--   Proposition 7, p. 10 — FPA equilibrium bidding formula
-- statement:
--   Under Assumption 1 there exists a symmetric increasing FPA CPE strategy, and every such strategy satisfies the following formula. Put $A_1(s)=f_1(s)V(s,s)+F_1(s)V_1(s,s)-\Psi_1(s,s)-\Omega_1(s,s)$, where subscript 1 differentiates in the first argument. For $t\in(\underline t,\overline t]$,
--
--   $$\beta_I(t)=\frac{\int_{\underline t}^{t}A_1(s)\,ds}{F_1(t)\{1+\Lambda^m[1-F_1(t)]\}}.$$
--
--   This gives both existence and the bidding formula for every symmetric increasing FPA CPE.
--
--   **Formalization Note** The displayed quotient is zero over zero at the lower endpoint, so the formula is asserted only above it.
-- source:
--   Balzer & Rosato, Expectations-Based Loss Aversion in Auctions with Interdependent Values, Management Science (Articles in Advance, 2020; doi:10.1287/mnsc.2019.3563), §4.1, Proposition 7 and eq. (11), p. 10 (PDF 11); proof p. 16 (PDF 17)

import Mathlib
import Definitions.Def_LossAverseAuction_CPERevenue_Model

namespace LossAverseAuction.CPERevenue

open MeasureTheory

theorem proposition_7 {m : ℕ} (E : Env m) (hS : E.Standing)
    (hA1 : E.Assumption1) :
    (∃ β : ℝ → ℝ, E.IsSymCPE .FPA β ∧
      ∀ t ∈ Set.Ioc E.tl E.th,
        β t = (∫ s in E.tl..t, E.A1 s) /
          (E.F1 t * (1 + E.Lm * (1 - E.F1 t)))) ∧
    ∀ β : ℝ → ℝ, E.IsSymCPE .FPA β →
      ∀ t ∈ Set.Ioc E.tl E.th,
        β t = (∫ s in E.tl..t, E.A1 s) /
          (E.F1 t * (1 + E.Lm * (1 - E.F1 t))) := by sorry
end LossAverseAuction.CPERevenue
