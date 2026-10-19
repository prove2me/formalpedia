-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_transpose_incidence_kernel
-- name    : OAI.PolynomialVacuumBridge.Corridor.transpose_incidence_kernel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:52:05.682771+00:00
-- url     : https://prove2.me/theorems/6f618154-380d-41ba-aee9-910fe937848e
-- title:
--   Flat functions on the cell of a simple loop are constant
-- statement:
--   Let $(g,w)$ be a closed walk on the honeycomb lattice ($\mathrm{terminalGerm}(g,w)=g$), let $q=\mathrm{wordFlow}(g,w)$ be its integer edge flow, and let $p$ be a finitely supported integer face potential representing $q$: the oriented flow at every germ equals $p(\mathrm{left})-p(\mathrm{right})$. The cell of $p$ is the set of faces in the support of $p$, with its cell edges and cell vertices. Assume the walk is nonempty and simple. Let $M$ be the vertex–edge incidence matrix of the cell of $\operatorname{supp}p$. Then the kernel of $M^{\top}$, i.e. the space of vertex functions flat along all cell edges, consists of the constant functions:
--   $$
--   \ker M^{\top}=\mathbb Q\cdot\mathbf 1 .
--   $$
--
--   The cell is connected through its edges.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Incidence.lean#L312-L359

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

theorem OAI.PolynomialVacuumBridge.Corridor.transpose_incidence_kernel (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) :
    (incidenceMatrix p.support).transpose.mulVecLin.ker =
      Submodule.span ℚ {(1 : cellVertices p.support → ℚ)} := by sorry
