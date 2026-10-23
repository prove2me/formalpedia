-- Prove2me | Theorems.Thm_MastSail_Monotone_proposition_5
-- name    : MastSail.Monotone.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:26.773142+00:00
-- url     : https://prove2.me/theorems/46ccaa3e-2385-42c1-a9da-7a7b843a1a66
-- title:
--   Proposition 5, p. 16 — a mast-and-sail plan is monotone in sales; monotone in inventory and jointly iff i_s = i_m, neither if i_s > i_m
-- statement:
--   Assume the standing assumptions of the model, valid weights $\omega$, any trigger $t$ and a positive bonus $\bar w>0$, and let $w$ be the plan (11) paying $\bar w$ on the mast-and-sail bonus region and $0$ elsewhere on $D$. Then
--
--   1. $w$ is monotone in $s$;
--   2. if $i_s=i_m$, then $w$ is also monotone in $i$ and (strictly) jointly monotone;
--   3. if $i_s>i_m$, then $w$ is neither monotone in $i$ nor jointly monotone.
--
--   In symbols, with the monotonicity notions of §6 on $D$,
--   $$w\ \text{monotone in } s,\qquad i_s=i_m\Rightarrow w\ \text{monotone in } i\ \text{and jointly},\qquad i_s>i_m\Rightarrow w\ \text{neither}.$$
--
--   The result exhibits the ex post moral hazard of mast-and-sail plans: when the mast starts strictly below the sail, the store manager can gain by destroying inventory.
--
--   **Formalization Note** The paper states the result for an optimal plan; it holds for every plan of the form (11), so optimality is dropped, which makes the statement stronger. $\bar w>0$ is needed: with $\bar w=0$ the plan is identically zero and part 3 fails. Joint monotonicity compares points with strictly larger inventory and strictly larger sales (footnote 8).
-- source:
--   Dai, Ke & Ryan, SSRN 3235866, p. 16, Proposition 5 (proof pp. oa6–oa7)

import Mathlib
import Definitions.Def_MastSail_Monotone_Model

namespace MastSail.Monotone
theorem proposition_5 (M : Model) (hM : M.Standing) (ω : Weights) (hω : ω.Valid) (t wbar : ℝ)
    (hw : 0 < wbar) :
    MonotoneInS M (plan M ω t wbar) ∧
    (iS M ω t = iM M ω t →
      MonotoneInI M (plan M ω t wbar) ∧ JointlyMonotone M (plan M ω t wbar)) ∧
    (iM M ω t < iS M ω t →
      ¬ MonotoneInI M (plan M ω t wbar) ∧ ¬ JointlyMonotone M (plan M ω t wbar)) := by sorry
end MastSail.Monotone
