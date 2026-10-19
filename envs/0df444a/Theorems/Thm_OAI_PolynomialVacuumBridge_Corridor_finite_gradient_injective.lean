-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_finite_gradient_injective
-- name    : OAI.PolynomialVacuumBridge.Corridor.finite_gradient_injective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:47:06.004884+00:00
-- url     : https://prove2.me/theorems/cad0a7f0-831c-4c20-916e-9306ea222246
-- title:
--   Finitely supported face functions are determined by their gradients
-- statement:
--   Faces of the honeycomb lattice are indexed by $\mathbb Z^2$, and the face gradient of a face function $r$ assigns to each edge $e$ the difference $r(\mathrm{left}(e))-r(\mathrm{right}(e))$ of its values on the two faces bordering $e$. If $r,s:\mathbb Z^2\to\mathbb Q$ are finitely supported and have the same face gradient, then
--   $$
--   r=s .
--   $$
--
--   So the face gradient is injective on finitely supported rational face functions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Currents.lean#L124-L145

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

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.finite_gradient_injective (r s : FaceIndex →₀ ℚ)
    (h : faceGradient r = faceGradient s) : r = s := by sorry
