-- Prove2me | Theorems.Thm_MediaMenus_Duopoly_consumer_choices
-- name    : MediaMenus.Duopoly.consumer_choices
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:52.52963+00:00
-- url     : https://prove2.me/theorems/e1d3ca67-1427-46ac-aa74-4c16c83df533
-- title:
--   Proof of Proposition 3, 'Consumer Choices', pp. 52–53 — at the stated menus each type optimally multi-homes on the item designed for her
-- statement:
--   Suppose both platforms offer the menu of Proposition 3,
--   $$(s^L,a^L)=\Big(\tfrac{\rho v^2}{2}-d^La^L-(d^H-d^L)a^H,\ \tfrac{w-d^L}{3}\Big),\qquad (s^H,a^H)=\Big(\tfrac{\rho v^2}{2}-d^Ha^H,\ \tfrac{\alpha}{3}\Big).$$
--   Then, under the standing assumptions, multi-homing with the $L$ item on both platforms is an admissible response of type $L$, and multi-homing with the $H$ item on both platforms is an admissible response of type $H$: each is utility-maximizing, and (as required on ties) multi-homing and participating.
--
--   This is the consumer half of the existence part of Proposition 3.
--
--   **Formalization Note.** "Admissible response" is `IsResponse` (tie rules 1–2). Type $L$ is indifferent between the two items on each platform, and type $H$ is indifferent between multi-homing and single-homing; both ties are resolved as on pp. 52–53.
-- source:
--   DeValve & Pekeč, Optimal Price/Advertising Menus for Two-Sided Media Platforms, SSRN 2715531 (version of 2021-04-15), pp. 52–53, proof of Proposition 3, 'Consumer Choices'

import Mathlib
import Definitions.Def_MediaMenus_Duopoly_Model

namespace MediaMenus.Duopoly

theorem consumer_choices (P : Params) (hS : P.Standing) :
    ∀ θ, IsResponse P θ (fun _ => eqMenu P) (eqChoice θ) := by sorry

end MediaMenus.Duopoly
