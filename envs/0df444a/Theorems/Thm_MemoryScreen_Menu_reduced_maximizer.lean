-- Prove2me | Theorems.Thm_MemoryScreen_Menu_reduced_maximizer
-- name    : MemoryScreen.Menu.reduced_maximizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:07.691705+00:00
-- url     : https://prove2.me/theorems/5ea00c54-e8b2-46dc-a138-d96bfc36d3cb
-- title:
--   Proof of Proposition 1, p. 28 — reduced-objective maximizer
-- statement:
--   The two-price objective $\Phi$ is globally maximized at
--
--   $$p_H=c,\qquad p_L=p_L^*=c+\frac{\theta}{1-\theta}(\alpha_H-\alpha_L).$$
--
--   If $f$ is strictly positive on an interval $(b_l,b_u)$ with $b_l<\alpha_L-p_L^*$ and $\alpha_H-c<b_u$, these are the unique maximizing prices. The positivity condition is the precise support-width condition needed for the paper's interior uniqueness claim.
-- source:
--   Guo, The Mnemonomics of Contractual Screening, SSRN preprint 3930657 (2022-03-13), p. 28 (PDF 29), proof of Proposition 1, optimal-interior-solution paragraph

import Mathlib
import Definitions.Def_MemoryScreen_Menu_Model

open MeasureTheory

namespace MemoryScreen.Menu

/-- The reduced objective is maximized at the prices printed in Proposition 1. -/
theorem reduced_maximizer (P : Params) (hS : P.Standing) :
    (∀ pH pL : ℝ, reducedObj P pH pL ≤ reducedObj P P.c (pStarL P)) ∧
    (∀ bl bu : ℝ, bl < P.αL - pStarL P → P.αH - P.c < bu →
      (∀ b ∈ Set.Ioo bl bu, 0 < P.f b) →
      ∀ pH pL : ℝ, reducedObj P pH pL = reducedObj P P.c (pStarL P) →
        pH = P.c ∧ pL = pStarL P) := by sorry

end MemoryScreen.Menu
