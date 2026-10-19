-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_contour_flat_trace
-- name    : OAI.PolynomialVacuumBridge.Corridor.contour_flat_trace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:51:30.029311+00:00
-- url     : https://prove2.me/theorems/0860f122-2df7-4f9f-be2e-0ab22ffadcd9
-- title:
--   Cell-flat functions are constant along a contour
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. Let $p$ be an integer face potential representing an edge chain $q$, and let $q$ be a word contour along $(g,w)$: at each step the oriented flow is $+1$ on the outgoing slot, $-1$ on the incoming slot and $0$ on the third. If $f$ is a vertex function flat along the cell edges of $\operatorname{supp}p$, then every vertex $v$ visited by the walk is a cell vertex and
--   $$
--   f(v)=f(g_1).
--   $$
--
--   So the boundary loop of a cell lies in the cell and carries a single value of any cell-flat function.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Incidence.lean#L285-L302

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

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.contour_flat_trace (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p q) (f : Vertex → ℚ)
    (hf : ∀ e ∈ cellEdges p.support, f (upEnd e) = f (downEnd e))
    (g : Germ) (w : List Bool) (hw : WordContour q g w) :
    ∀ v ∈ traced g w, v ∈ cellVertices p.support ∧ f v = f g.1 := by sorry
