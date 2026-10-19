-- Prove2me | Theorems.Thm_MediaMenus_Duopoly_lemma_6_e
-- name    : MediaMenus.Duopoly.lemma_6_e
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:46.475439+00:00
-- url     : https://prove2.me/theorems/85151a7a-551d-42a1-aec5-bb173e33cbc4
-- title:
--   Lemma 6 E, p. 45 — on each platform the consumer uses, her chosen item minimizes d^θ a + s over that platform's menu
-- statement:
--   Consider the duopoly with two-item menus, and suppose a consumer of type $\theta$ makes an optimal choice that uses item $(s_i,a_i)$ of platform $i$, whether she single-homes or multi-homes. Then, under the standing assumptions, for every item $(s'_i,a'_i)$ of platform $i$'s menu,
--   $$d^\theta a_i+s_i\le d^\theta a'_i+s'_i .$$
--
--   Item choice on a platform therefore depends only on that platform's menu, which is what lets each platform's best-response problem be written separately.
--
--   **Formalization Note.** "Uses option $\phi_i$" is read as an optimal choice whose item slot on platform $i$ is $\phi_i$. The paper states the inequality for $\phi'_i\ne\phi_i$; for $\phi'_i=\phi_i$ it is trivial, so the Lean quantifies over all slots.
-- source:
--   DeValve & Pekeč, Optimal Price/Advertising Menus for Two-Sided Media Platforms, SSRN 2715531 (version of 2021-04-15), p. 45, Lemma 6 E

import Mathlib
import Definitions.Def_MediaMenus_Duopoly_Model

namespace MediaMenus.Duopoly

theorem lemma_6_e (P : Params) (hS : P.Standing) (M : Profile) (θ : Ty) (c : Choice)
    (hopt : IsOptimal P θ M c) (i k : Fin 2) (hk : c.itemOn i = some k) :
    ∀ k' : Fin 2, cost P θ (M i k) ≤ cost P θ (M i k') := by sorry

end MediaMenus.Duopoly
