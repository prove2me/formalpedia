-- Prove2me | Theorems.Thm_MastSail_Monotone_proposition_3
-- name    : MastSail.Monotone.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:29.463614+00:00
-- url     : https://prove2.me/theorems/6f3b986b-29d9-452b-9f82-04e8822aff56
-- title:
--   Proposition 3, p. 14 — in every plan of the form (11), i_s ≥ i_m
-- statement:
--   Assume the standing assumptions of the model and valid weights $\omega$, and let $t$ be any trigger. Then the critical inventories of the plan (11) satisfy
--   $$i_s\ge i_m .$$
--
--   So the mast always starts at or below the sail: only the structure of Figure 2(a) occurs, never the "mast too short for its sail" of Figure 2(b).
--
--   **Formalization Note** The paper states this for an optimal plan; the statement holds for every weight vector and every trigger, so optimality is dropped, which makes it stronger.
-- source:
--   Dai, Ke & Ryan, SSRN 3235866, p. 14, Proposition 3 (proof pp. oa5–oa6)

import Mathlib
import Definitions.Def_MastSail_Monotone_Model

namespace MastSail.Monotone
theorem proposition_3 (M : Model) (hM : M.Standing) (ω : Weights) (hω : ω.Valid) (t : ℝ) :
    iM M ω t ≤ iS M ω t := by sorry
end MastSail.Monotone
