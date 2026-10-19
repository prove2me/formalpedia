-- Prove2me | Theorems.Thm_MediaMenus_Duopoly_best_response_22_24
-- name    : MediaMenus.Duopoly.best_response_22_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:59.574569+00:00
-- url     : https://prove2.me/theorems/c194cff9-6b5a-4ebf-9dc4-50633f1a91e1
-- title:
--   Proof of Proposition 3, (22) and (24), pp. 56–58 — in every equilibrium each platform's chosen items are the best response (22)/(24) to the rival's
-- statement:
--   Consider an equilibrium of the duopoly in which type $L$ multi-homes on items $(s^L_1,a^L_1)$, $(s^L_2,a^L_2)$ and type $H$ on items $(s^H_1,a^H_1)$, $(s^H_2,a^H_2)$ of platforms 1 and 2. Write $r^L=1-r$, $r^H=r$, and let $j$ be the rival of platform $i$. Then, under the standing assumptions, the ad quantities chosen on platform $i$ are
--   $$a^L_i=\Big(\max\Big(\tfrac{w-d^L-a^L_j}{2},\ \tfrac{w-d^H-(r^La^L_j+r^Ha^H_j)}{2}\Big)\Big)^+,\qquad a^H_i=\Big(\min\Big(\tfrac{r^H(w-d^H-a^H_j)-r^L(d^H-d^L)}{2r^H},\ \tfrac{w-d^H-(r^La^L_j+r^Ha^H_j)}{2}\Big)\Big)^+,$$
--   display (22), and the prices are
--   $$s^L_i=\frac{(1-\gamma)v^2}{2(1+\gamma)}-d^La^L_i-(d^H-d^L)a^H_i,\qquad s^H_i=\frac{(1-\gamma)v^2}{2(1+\gamma)}-d^Ha^H_i,$$
--   display (24).
--
--   This is the best-response correspondence of the duopoly; with Lemma 8 it reduces uniqueness of equilibrium to the fixed-point equations of (22).
--
--   **Formalization Note.** The chosen slots are given by `k : Ty → Fin 2 → Fin 2` with `c θ = multi (k θ 0) (k θ 1)`; Lemma 8 shows every equilibrium has this form. The paper derives (22)/(24) as the optimal solution of its program (21) and uses, in the uniqueness argument, that an equilibrium menu solves (21); here the statement is about `IsEquilibrium` directly.
-- source:
--   DeValve & Pekeč, Optimal Price/Advertising Menus for Two-Sided Media Platforms, SSRN 2715531 (version of 2021-04-15), pp. 56–58, proof of Proposition 3, 'Uniqueness', displays (22) and (24)

import Mathlib
import Definitions.Def_MediaMenus_Duopoly_Model

namespace MediaMenus.Duopoly

theorem best_response_22_24 (P : Params) (hS : P.Standing) (M : Profile) (c : Ty → Choice)
    (hE : IsEquilibrium P M c) (k : Ty → Fin 2 → Fin 2)
    (hk : ∀ θ, c θ = .multi (k θ 0) (k θ 1)) (i : Fin 2) :
    (M i (k .L i)).2 = brAdL P (M (other i) (k .L (other i))).2 (M (other i) (k .H (other i))).2 ∧
    (M i (k .H i)).2 = brAdH P (M (other i) (k .L (other i))).2 (M (other i) (k .H (other i))).2 ∧
    (M i (k .L i)).1 = brPriceL P (M i (k .L i)).2 (M i (k .H i)).2 ∧
    (M i (k .H i)).1 = brPriceH P (M i (k .H i)).2 := by sorry

end MediaMenus.Duopoly
