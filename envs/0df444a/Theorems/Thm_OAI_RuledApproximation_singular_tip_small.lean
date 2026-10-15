-- Prove2me | Theorems.Thm_OAI_RuledApproximation_singular_tip_small
-- name    : OAI.RuledApproximation.singular_tip_small
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:11:58.691541+00:00
-- url     : https://prove2.me/theorems/89553403-3b24-47c2-8005-baccbe898949
-- title:
--   For $\gamma>1$, $(c^\gamma)^2=o(c^2)$ as $c\to0^+$
-- statement:
--   Let $\gamma>1$ be a real number. Then, as $c$ tends to $0$ through positive values,
--
--   $$
--   (c^\gamma)^2=o(c^2)\qquad(c\to0^+),
--   $$
--
--   that is, $(c^\gamma)^2/c^2\to0$ as $c\to0^+$.
--
--   In the singular part of the main covering theorem for the regular tetrahedron, the quantity expanded to order $c^2$ is $2\,\mathrm{cost}_{p,\gamma}(c)+8\sqrt2\,(c^\gamma)^2$, where the second term is the total cross-sectional area of the two triangular tip cylinders, whose size is proportional to $c^\gamma$. The lemma shows that this tip term does not contribute at order $c^2$ as long as $\gamma>1$.
--
--   **Formalization Note** The statement is `Asymptotics.IsLittleO (𝓝[>] 0) (fun c => (c^gamma)^2) (fun c => c^2)`, i.e. little-o along the filter of right neighbourhoods of $0$; $c^\gamma$ is the real power `Real.rpow` and the squares are natural-number powers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SingularBounds.lean#L102-L116

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.singular_tip_small {gamma : ℝ} (hg : 1 < gamma) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ)) (fun c : ℝ => (c^gamma)^2) (fun c => c^2) := by sorry
