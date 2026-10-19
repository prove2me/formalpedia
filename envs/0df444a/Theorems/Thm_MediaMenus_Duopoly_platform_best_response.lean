-- Prove2me | Theorems.Thm_MediaMenus_Duopoly_platform_best_response
-- name    : MediaMenus.Duopoly.platform_best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:55.712151+00:00
-- url     : https://prove2.me/theorems/de8d6bcd-139c-4865-9c86-afeb7e473a90
-- title:
--   Proof of Proposition 3, 'Platform Best Response', pp. 53–56 — against the stated menu no deviation earns more than ρv²/2 + [(1−r)(w−d^L)² + rα²]/9
-- statement:
--   Suppose platform $j$ offers the menu of Proposition 3 and platform $i$ deviates to an arbitrary admissible two-item menu $M'$ (ad quantities $\ge0$, prices unrestricted). Let the consumers respond to the deviated profile by any choices that are utility-maximizing, multi-home and participate on ties, and in which a type that uses platform $j$ keeps the item she chose there before the deviation. Then, under the standing assumptions, platform $i$'s expected revenue is at most
--   $$\frac{\rho v^2}{2}+\frac{(1-r)(w-d^L)^2+r\alpha^2}{9},$$
--   which is its revenue at the stated profile.
--
--   With the consumer-choice step this gives the existence part of Proposition 3: the symmetric profile is an equilibrium.
--
--   **Formalization Note.** The deviated profile is `Function.update (fun _ => eqMenu P) i M'`; the status-quo clause refers to `eqChoice` on the rival platform `other i`. The bound holds for every response allowed by the rules, which is the deviator choosing its most favourable one.
-- source:
--   DeValve & Pekeč, Optimal Price/Advertising Menus for Two-Sided Media Platforms, SSRN 2715531 (version of 2021-04-15), pp. 53–56, proof of Proposition 3, 'Platform Best Response'

import Mathlib
import Definitions.Def_MediaMenus_Duopoly_Model

namespace MediaMenus.Duopoly

theorem platform_best_response (P : Params) (hS : P.Standing) (i : Fin 2) :
    expRev P (fun _ => eqMenu P) i eqChoice =
      rho P * P.v ^ 2 / 2 + ((1 - P.r) * (P.w - P.dL) ^ 2 + P.r * alphaQ P ^ 2) / 9 ∧
    ∀ (M' : Menu), M'.Admissible → ∀ c' : Ty → Choice,
      (∀ θ, IsResponse P θ (Function.update (fun _ => eqMenu P) i M') (c' θ)) →
      (∀ θ k k', (eqChoice θ).itemOn (other i) = some k →
        (c' θ).itemOn (other i) = some k' → k' = k) →
      expRev P (Function.update (fun _ => eqMenu P) i M') i c' ≤
        rho P * P.v ^ 2 / 2 + ((1 - P.r) * (P.w - P.dL) ^ 2 + P.r * alphaQ P ^ 2) / 9 := by sorry

end MediaMenus.Duopoly
