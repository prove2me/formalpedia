-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_cell_flat_zero_boundary
-- name    : OAI.PolynomialVacuumBridge.Corridor.cell_flat_zero_boundary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:49:50.580082+00:00
-- url     : https://prove2.me/theorems/9d458ccf-ac0f-4c67-afca-1d9e2c6e2d31
-- title:
--   Flat vertex functions on a loop cell vanishing on the loop are zero
-- statement:
--   Let $(g,w)$ be a closed walk on the honeycomb lattice ($\mathrm{terminalGerm}(g,w)=g$), let $q=\mathrm{wordFlow}(g,w)$ be its integer edge flow, and let $p$ be a finitely supported integer face potential representing $q$: the oriented flow at every germ equals $p(\mathrm{left})-p(\mathrm{right})$. The cell of $p$ is the set of faces in the support of $p$, with its cell edges and cell vertices. Let $f$ be a finitely supported rational vertex function with support among the cell vertices. Suppose $f$ is flat along cell edges, $f(\mathrm{up}(e))=f(\mathrm{down}(e))$ for every cell edge $e$, and vanishes at every vertex visited by the walk. Then
--   $$
--   f=0 .
--   $$
--
--   Thus a flat function on the cell is determined by its value on the boundary loop.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/PotentialSupport.lean#L165-L183

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

theorem OAI.PolynomialVacuumBridge.Corridor.cell_flat_zero_boundary (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w))
    (f : Vertex →₀ ℚ) (hS : f.support ⊆ cellVertices p.support)
    (hflat : ∀ e ∈ cellEdges p.support, f (upEnd e) = f (downEnd e))
    (hbd : ∀ v ∈ traced g w, f v = 0) : f = 0 := by sorry
