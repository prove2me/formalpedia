-- Prove2me | Theorems.Thm_MediaMenus_Duopoly_lemma_6_c
-- name    : MediaMenus.Duopoly.lemma_6_c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:51.16338+00:00
-- url     : https://prove2.me/theorems/109b887d-cd1a-4fa6-b53c-e5764318a202
-- title:
--   Lemma 6 C, p. 45 — if multi-homing is optimal, each chosen item costs at most (1−γ)v²/(2(1+γ))
-- statement:
--   Consider the duopoly with two-item menus, and suppose that multi-homing with item $(s_1,a_1)$ from platform 1 and item $(s_2,a_2)$ from platform 2 is an optimal choice for a consumer of type $\theta$. Then, under the standing assumptions, for each $i\in\{1,2\}$
--   $$d^\theta a_i+s_i\le\frac{(1-\gamma)v^2}{2(1+\gamma)}.$$
--
--   The threshold $(1-\gamma)v^2/(2(1+\gamma))$ is the extra utility the second platform adds to a consumer already using the first; this lemma is the participation constraint of a multi-homing consumer on each platform.
--
--   **Formalization Note.** "Multi-homes" is read as "multi-homing is an optimal choice" (`IsOptimal`), the consumer-optimality condition under which the paper uses the lemma.
-- source:
--   DeValve & Pekeč, Optimal Price/Advertising Menus for Two-Sided Media Platforms, SSRN 2715531 (version of 2021-04-15), p. 45, Lemma 6 C

import Mathlib
import Definitions.Def_MediaMenus_Duopoly_Model

namespace MediaMenus.Duopoly

theorem lemma_6_c (P : Params) (hS : P.Standing) (M : Profile) (θ : Ty) (k₀ k₁ : Fin 2)
    (hopt : IsOptimal P θ M (.multi k₀ k₁)) :
    cost P θ (M 0 k₀) ≤ (1 - P.γ) * P.v ^ 2 / (2 * (1 + P.γ)) ∧
      cost P θ (M 1 k₁) ≤ (1 - P.γ) * P.v ^ 2 / (2 * (1 + P.γ)) := by sorry

end MediaMenus.Duopoly
