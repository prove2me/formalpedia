-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_potential_supported_on_cycle_cells
-- name    : OAI.PolynomialVacuumBridge.Corridor.potential_supported_on_cycle_cells
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:48:34.15999+00:00
-- url     : https://prove2.me/theorems/8a08faab-499f-4401-836b-c29227b5e03b
-- title:
--   Face functions with gradient inside a simple loop's cell live in the cell
-- statement:
--   Let $(g,w)$ be a closed walk on the honeycomb lattice ($\mathrm{terminalGerm}(g,w)=g$), let $q=\mathrm{wordFlow}(g,w)$ be its integer edge flow, and let $p$ be a finitely supported integer face potential representing $q$: the oriented flow at every germ equals $p(\mathrm{left})-p(\mathrm{right})$. The cell of $p$ is the set of faces in the support of $p$, with its cell edges and cell vertices. Assume the closed walk is simple and $p\ne0$. If a finitely supported rational face function $r$ has zero face gradient on every edge outside the cell edges of $\operatorname{supp}p$, then
--   $$
--   \operatorname{supp}r\subseteq\operatorname{supp}p .
--   $$
--
--   A potential that is flat outside the loop's cell must vanish outside it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/PotentialSupport.lean#L39-L90

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

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.potential_supported_on_cycle_cells (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) (hpne : p ≠ 0)
    (r : FaceIndex →₀ ℚ)
    (hr : ∀ e, e ∉ cellEdges p.support → faceGradient r e = 0) :
    r.support ⊆ p.support := by sorry
