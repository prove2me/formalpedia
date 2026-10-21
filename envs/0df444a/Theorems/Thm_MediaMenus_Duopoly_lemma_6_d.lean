-- Prove2me | Theorems.Thm_MediaMenus_Duopoly_lemma_6_d
-- name    : MediaMenus.Duopoly.lemma_6_d
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:47.961157+00:00
-- url     : https://prove2.me/theorems/f6ce8d67-aa91-49c2-a6ba-905c602911bd
-- title:
--   Lemma 6 D, p. 45 — if single-homing on i is optimal, every item of the rival costs at least (1−γ)v²/(2(1+γ))
-- statement:
--   Consider the duopoly with two-item menus, and suppose that single-homing on platform $i$ with some item is an optimal choice for a consumer of type $\theta$. Then, under the standing assumptions, every item $(s_{i'},a_{i'})$ of the other platform $i'$ satisfies
--   $$d^\theta a_{i'}+s_{i'}\ge\frac{(1-\gamma)v^2}{2(1+\gamma)}.$$
--
--   This is the counterpart of Lemma 6 C: a single-homing consumer finds no item of the rival cheap enough to add.
--
--   **Formalization Note.** "Single-homes" is read as "single-homing is an optimal choice" (`IsOptimal`). The rival platform is `other i`.
-- source:
--   DeValve & Pekeč, Optimal Price/Advertising Menus for Two-Sided Media Platforms, SSRN 2715531 (version of 2021-04-15), p. 45, Lemma 6 D

import Mathlib
import Definitions.Def_MediaMenus_Duopoly_Model

namespace MediaMenus.Duopoly

theorem lemma_6_d (P : Params) (hS : P.Standing) (M : Profile) (θ : Ty) (i k : Fin 2)
    (hopt : IsOptimal P θ M (.single i k)) :
    ∀ k' : Fin 2, (1 - P.γ) * P.v ^ 2 / (2 * (1 + P.γ)) ≤ cost P θ (M (other i) k') := by sorry

end MediaMenus.Duopoly
