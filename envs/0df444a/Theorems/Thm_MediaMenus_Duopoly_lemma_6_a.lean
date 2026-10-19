-- Prove2me | Theorems.Thm_MediaMenus_Duopoly_lemma_6_a
-- name    : MediaMenus.Duopoly.lemma_6_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:44.219297+00:00
-- url     : https://prove2.me/theorems/2bfdbd97-6515-4099-8218-e65b46d30f03
-- title:
--   Lemma 6 A, p. 45 — a multi-homing consumer earns v²/(1+γ) minus the costs of her two items
-- statement:
--   Consider the duopoly with two-item menus, and let a consumer of type $\theta$ multi-home with item $(s_1,a_1)$ from platform 1 and item $(s_2,a_2)$ from platform 2. Under the standing assumptions, the supremum over $x_1,x_2\ge 0$ of the multi-homing utility (2) equals
--   $$\frac{v^2}{1+\gamma}-\sum_{i=1}^{2}\big(d^\theta a_i+s_i\big).$$
--
--   This is the closed form of the multi-homing utility used throughout the duopoly analysis to compare homing choices.
--
--   **Formalization Note.** The utility of a choice is defined as a supremum over nonnegative consumption, not by this formula; the statement holds for every menu profile, admissible or not.
-- source:
--   DeValve & Pekeč, Optimal Price/Advertising Menus for Two-Sided Media Platforms, SSRN 2715531 (version of 2021-04-15), p. 45, Lemma 6 A

import Mathlib
import Definitions.Def_MediaMenus_Duopoly_Model

namespace MediaMenus.Duopoly

theorem lemma_6_a (P : Params) (hS : P.Standing) (M : Profile) (θ : Ty) (k₀ k₁ : Fin 2) :
    utility P θ M (.multi k₀ k₁) =
      P.v ^ 2 / (1 + P.γ) - (cost P θ (M 0 k₀) + cost P θ (M 1 k₁)) := by sorry

end MediaMenus.Duopoly
