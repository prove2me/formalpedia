-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_conserved_finite_potential
-- name    : OAI.PolynomialVacuumBridge.Corridor.conserved_finite_potential
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:47:46.070234+00:00
-- url     : https://prove2.me/theorems/76e0693b-bcd4-4d34-95b0-57e177293589
-- title:
--   Finite conserved currents are face gradients
-- statement:
--   Faces of the honeycomb lattice are indexed by $\mathbb Z^2$, and the face gradient of a face function $r$ assigns to each edge $e$ the difference $r(\mathrm{left}(e))-r(\mathrm{right}(e))$ of its values on the two faces bordering $e$. A finitely supported rational edge function $q$ is a conserved current if at every vertex $v$ the directed currents through the three slots sum to zero, $\sum_{k}\mathrm{sign}(v)\,q(\mathrm{edge}(v,k))=0$. Every such $q$ is the gradient of a finitely supported face function:
--   $$
--   \exists\,r:\mathbb Z^2\to\mathbb Q\ \text{finitely supported},\qquad\nabla r=q .
--   $$
--
--   This is the discrete Poincaré lemma for the planar honeycomb lattice.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/PotentialSupport.lean#L13-L37

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

theorem OAI.PolynomialVacuumBridge.Corridor.conserved_finite_potential (q : EdgeIndex →₀ ℚ) (hq : ConservedCurrent q) :
    ∃ r : FaceIndex →₀ ℚ, faceGradient r = q := by sorry
