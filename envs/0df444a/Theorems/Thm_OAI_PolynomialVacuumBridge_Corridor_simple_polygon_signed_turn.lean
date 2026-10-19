-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_simple_polygon_signed_turn
-- name    : OAI.PolynomialVacuumBridge.Corridor.simple_polygon_signed_turn
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:53:11.28211+00:00
-- url     : https://prove2.me/theorems/5b7e0996-e653-437b-a4a1-c9ca21dc1f16
-- title:
--   Turning number of a simple closed honeycomb walk
-- statement:
--   Let $(g,w)$ be a closed walk on the honeycomb lattice ($\mathrm{terminalGerm}(g,w)=g$), let $q=\mathrm{wordFlow}(g,w)$ be its integer edge flow, and let $p$ be a finitely supported integer face potential representing $q$: the oriented flow at every germ equals $p(\mathrm{left})-p(\mathrm{right})$. The cell of $p$ is the set of faces in the support of $p$, with its cell edges and cell vertices. Assume the walk is nonempty and simple, $p\ne0$, and $p$ takes only the values $0$ and $\varepsilon\in\{1,-1\}$. Then the number of left turns minus right turns satisfies
--   $$
--   \varepsilon\cdot\mathrm{turnUnits}(w)=6 .
--   $$
--
--   So a simple loop turns by exactly $\pm2\pi$, with sign given by its orientation: this is the discrete Hopf Umlaufsatz.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Polygons.lean#L15-L37

import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.simple_polygon_signed_turn (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (ε : ℤ) (hp : RepresentsFlow p (wordFlow g w))
    (hpne : p ≠ 0) (hε : ε = 1 ∨ ε = -1)
    (hvals : ∀ a, p a = 0 ∨ p a = ε) : ε * turnUnits w = 6 := by sorry
