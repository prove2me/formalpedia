-- Prove2me | Theorems.Thm_MemoryScreen_Menu_information_rent
-- name    : MemoryScreen.Menu.information_rent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:59.269678+00:00
-- url     : https://prove2.me/theorems/a358ab85-7826-4994-a2f1-f52dcbff3ae3
-- title:
--   §3.2.1, pp. 11–12 — affine payoff and high-type information rent
-- statement:
--   For a fixed tariff $(T,p)$ and stage-two belief $\widetilde\alpha$, the expected payoff is affine in the buyer's true type:
--
--   $$EU(T,p;\alpha',\widetilde\alpha)-EU(T,p;\alpha,\widetilde\alpha)=(\alpha'-\alpha)F(\widetilde\alpha-p).$$
--
--   In particular, choosing the low-type tariff gives the high type information rent $R(p_L)=(\alpha_H-\alpha_L)F(\alpha_L-p_L)$. The deviation retains the low contract's stage-two belief $\alpha_L$, which is the source of the limited-memory rent formula.
--
--   **Formalization Note.** The paper prints $db$ in the displayed rent integrals on p. 12; consistent with equation (5), this statement integrates against $dF(b)=f(b)db$.
-- source:
--   Guo, The Mnemonomics of Contractual Screening, SSRN preprint 3930657 (2022-03-13), pp. 11–12 (PDF 12–13), §3.2.1, affine-payoff and information-rent paragraphs

import Mathlib
import Definitions.Def_MemoryScreen_Menu_Model

open MeasureTheory

namespace MemoryScreen.Menu

/-- The affine-type payoff identity and limited-memory information rent of §3.2.1. -/
theorem information_rent (P : Params) (hS : P.Standing) :
    (∀ (T p α α' αt : ℝ),
      EU P T p α' αt - EU P T p α αt = (α' - α) * F P (αt - p)) ∧
    (∀ (T pL : ℝ),
      EU P T pL P.αH P.αL - EU P T pL P.αL P.αL =
        (P.αH - P.αL) * F P (P.αL - pL)) := by sorry

end MemoryScreen.Menu
