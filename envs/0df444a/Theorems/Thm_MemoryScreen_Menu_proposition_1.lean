-- Prove2me | Theorems.Thm_MemoryScreen_Menu_proposition_1
-- name    : MemoryScreen.Menu.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:04.906403+00:00
-- url     : https://prove2.me/theorems/b55a34ae-2a09-4db0-94cf-748e0883a0da
-- title:
--   Proposition 1, p. 12 — optimal menu under limited memory
-- statement:
--   For the two-type limited-memory screening program (6), an optimal menu exists with marginal prices
--
--   $$p_H^*=c,\qquad p_L^*=c+\frac{\theta}{1-\theta}(\alpha_H-\alpha_L).$$
--
--   If the density is positive across an interval containing both transaction thresholds, every optimal menu has those prices. Let $p_L^B$ be the globally maximizing low-type price in the perfect-memory objective (4), with the objective rising to its peak and falling after it on a neighborhood containing $p_L^*$ and $p_L^B$. Then
--
--   $$p_L^*<p_L^B\quad\Longleftrightarrow\quad f(\alpha_L-p_L^*)<\frac{F(\alpha_H-p_L^*)-F(\alpha_L-p_L^*)}{\alpha_H-\alpha_L}.$$
--
--   Thus forgetting can reduce or increase the upward distortion of the low-type marginal price relative to perfect memory.
--
--   **Formalization Note.** Optimality means optimality among all menus satisfying the weak IR and limited-memory IC inequalities of program (6). The model assumes a finite first moment; uniqueness additionally assumes positive density on the stated interval. The single-peakedness hypothesis is local around the compared prices, with a global maximizing peak.
-- source:
--   Guo, The Mnemonomics of Contractual Screening, SSRN preprint 3930657 (2022-03-13), p. 12 (PDF 13), Proposition 1; support condition p. 28 (PDF 29), proof of Proposition 1

import Mathlib
import Definitions.Def_MemoryScreen_Menu_Model

open MeasureTheory

namespace MemoryScreen.Menu

/-- Proposition 1: optimal prices under limited memory and their comparison with perfect memory. -/
theorem proposition_1 (P : Params) (hS : P.Standing) :
    (∃ M : Menu, IsOptimal P M ∧ M.pH = P.c ∧ M.pL = pStarL P) ∧
    (∀ bl bu : ℝ, bl < P.αL - pStarL P → P.αH - P.c < bu →
      (∀ b ∈ Set.Ioo bl bu, 0 < P.f b) →
      ∀ M : Menu, IsOptimal P M → M.pH = P.c ∧ M.pL = pStarL P) ∧
    (∀ pB lo hi : ℝ, PeakedAt (perfectObj P P.c) pB lo hi →
      pStarL P ∈ Set.Ioo lo hi →
      (pStarL P < pB ↔
        P.f (P.αL - pStarL P) <
          (F P (P.αH - pStarL P) - F P (P.αL - pStarL P)) /
            (P.αH - P.αL))) := by sorry

end MemoryScreen.Menu
