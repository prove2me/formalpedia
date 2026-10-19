-- Prove2me | Theorems.Thm_MediaMenus_Duopoly_lemma_6_b
-- name    : MediaMenus.Duopoly.lemma_6_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:48.320425+00:00
-- url     : https://prove2.me/theorems/b5fffe06-9889-408d-bea4-bea7a457098a
-- title:
--   Lemma 6 B, p. 45 — a single-homing consumer earns v²/2 minus the cost of her item
-- statement:
--   Consider the duopoly with two-item menus, and let a consumer of type $\theta$ single-home on platform $i$ with item $(s_i,a_i)$. Under the standing assumptions, the supremum over $x_i\ge0$ of the single-homing utility (1) equals
--   $$\tfrac12 v^2-\big(d^\theta a_i+s_i\big).$$
--
--   Together with Lemma 6 A this reduces every comparison of homing choices to a comparison of item costs $d^\theta a+s$.
--
--   **Formalization Note.** The utility is defined as a supremum over $x_i\ge0$; the statement holds for every menu profile.
-- source:
--   DeValve & Pekeč, Optimal Price/Advertising Menus for Two-Sided Media Platforms, SSRN 2715531 (version of 2021-04-15), p. 45, Lemma 6 B

import Mathlib
import Definitions.Def_MediaMenus_Duopoly_Model

namespace MediaMenus.Duopoly

theorem lemma_6_b (P : Params) (hS : P.Standing) (M : Profile) (θ : Ty) (i k : Fin 2) :
    utility P θ M (.single i k) = P.v ^ 2 / 2 - cost P θ (M i k) := by sorry

end MediaMenus.Duopoly
