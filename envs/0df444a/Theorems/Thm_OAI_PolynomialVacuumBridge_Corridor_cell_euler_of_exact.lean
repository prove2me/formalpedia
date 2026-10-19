-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_cell_euler_of_exact
-- name    : OAI.PolynomialVacuumBridge.Corridor.cell_euler_of_exact
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:50:52.32871+00:00
-- url     : https://prove2.me/theorems/1f8e8e7c-c0c2-489f-8c07-45362398cfbe
-- title:
--   Euler characteristic one from an exact cell complex
-- statement:
--   Let $V,E,F$ be finite sets with $V$ nonempty, let $A:\mathbb Q^E\to\mathbb Q^V$ be given by a matrix (the vertex–edge incidence) and $B:\mathbb Q^F\to\mathbb Q^E$ a linear map (the face boundary). Assume that $B$ is injective, that $\operatorname{im}B=\ker A$, and that $\ker A^{\top}$ is spanned by the constant vector $\mathbf 1$. Then
--   $$
--   |V|-|E|+|F|=1 .
--   $$
--
--   This is the Euler formula for a contractible two-dimensional cell complex, derived from exactness of its chain complex.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/EulerRank.lean#L9-L31

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

theorem OAI.PolynomialVacuumBridge.Corridor.cell_euler_of_exact {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [Nonempty V]
    (A : Matrix V E ℚ) (B : (F → ℚ) →ₗ[ℚ] (E → ℚ))
    (hB : Function.Injective B) (hex : B.range = A.mulVecLin.ker)
    (hconst : A.transpose.mulVecLin.ker = Submodule.span ℚ {(1 : V → ℚ)}) :
    (Fintype.card V : ℤ) - Fintype.card E + Fintype.card F = 1 := by sorry
