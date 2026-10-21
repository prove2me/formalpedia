-- Prove2me | Theorems.Thm_MediaMenus_Duopoly_lemma_8
-- name    : MediaMenus.Duopoly.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:44.59022+00:00
-- url     : https://prove2.me/theorems/7de45d57-785c-4a00-8122-83b507150180
-- title:
--   Lemma 8, p. 47 — there is no duopoly equilibrium in which either consumer type does not multi-home
-- statement:
--   In the duopoly with two-item menus, under the standing assumptions, every equilibrium (in the sense of the model file: consumer optimality, multi-homing and participation on ties, arbitrary admissible deviations, status quo on the rival platform) has both consumer types multi-homing:
--   $$\text{for every equilibrium and every }\theta\in\{L,H\},\ \text{type }\theta\text{ multi-homes}.$$
--
--   This rules out every combination of single-homing and abstention in equilibrium, and reduces the search for equilibria to profiles where each platform serves both types.
--
--   **Formalization Note.** The conclusion is that the choice of each type is a `multi` choice. The equilibrium concept is `IsEquilibrium` of the model file.
-- source:
--   DeValve & Pekeč, Optimal Price/Advertising Menus for Two-Sided Media Platforms, SSRN 2715531 (version of 2021-04-15), p. 47, Lemma 8 (proof pp. 47–52)

import Mathlib
import Definitions.Def_MediaMenus_Duopoly_Model

namespace MediaMenus.Duopoly

theorem lemma_8 (P : Params) (hS : P.Standing) (M : Profile) (c : Ty → Choice)
    (hE : IsEquilibrium P M c) : ∀ θ, (c θ).IsMulti := by sorry

end MediaMenus.Duopoly
