-- Prove2me | Theorems.Thm_MemoryScreen_Menu_integration_by_parts
-- name    : MemoryScreen.Menu.integration_by_parts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:49.951811+00:00
-- url     : https://prove2.me/theorems/7503451a-8587-41f5-a231-2dfb1615058e
-- title:
--   §3.1, p. 10 — integration by parts for the buyer payoff
-- statement:
--   Let $F(x)=\int_{-\infty}^x f(b)\,db$ for the model's transaction-cost density. For every real $x$,
--
--   $$\int_{-\infty}^{x}(x-b)f(b)\,db=\int_{-\infty}^{x}F(b)\,db.$$
--
--   Consequently, for a tariff $(T,p)$ and a buyer who remembers true type $\alpha$, $EU(T,p;\alpha,\alpha)=\int_{-\infty}^{\alpha-p}F(b)\,db-T$. This identity is used in the objectives for both memory regimes. The finite first moment makes the left integral well defined.
-- source:
--   Guo, The Mnemonomics of Contractual Screening, SSRN preprint 3930657 (2022-03-13), p. 10 (PDF 11), §3.1, integration-by-parts sentence before eq. (4)

import Mathlib
import Definitions.Def_MemoryScreen_Menu_Model

open MeasureTheory

namespace MemoryScreen.Menu

/-- The integration-by-parts step of §3.1, used to rewrite the buyer's payoff. -/
theorem integration_by_parts (P : Params) (hS : P.Standing) :
    (∀ x : ℝ, (∫ b in Set.Iic x, (x - b) * P.f b) =
      ∫ b in Set.Iic x, F P b) ∧
    (∀ T p α : ℝ, EU P T p α α = (∫ b in Set.Iic (α - p), F P b) - T) := by sorry

end MemoryScreen.Menu
