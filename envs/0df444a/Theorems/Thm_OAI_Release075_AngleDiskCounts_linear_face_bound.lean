-- Prove2me | Theorems.Thm_OAI_Release075_AngleDiskCounts_linear_face_bound
-- name    : OAI.Release075.AngleDiskCounts.linear_face_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:03:23.906987+00:00
-- url     : https://prove2.me/theorems/85de731d-0eb1-486e-8653-3ebd0bcac09a
-- title:
--   Linear isoperimetric inequality from large interior angles
-- statement:
--   Angle disk counts consist of finitely many vertices with boundary visits $\mathrm{vis}(v)\in\mathbb N$ and angles $\theta(v)\ge0$, together with numbers $E$ of edges and $F$ of faces, satisfying $|V|+F=E+1$, $\sum_v\mathrm{vis}(v)+3F=2E$ and $\sum_v\theta(v)=5F$. The curvature is $\kappa(v)=10-5\,\mathrm{vis}(v)-\theta(v)$ (so $10$ stands for a full turn), and the boundary length is $\sum_v\mathrm{vis}(v)$. If every interior vertex ($\mathrm{vis}=0$) has angle at least $12$, then
--   $$
--   F+12\le6\cdot\mathrm{boundary\ length}.
--   $$
--
--   So the number of faces is bounded linearly by the boundary length.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Ribbons.lean#L95-L112

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons

open OAI OAI.Release075 OAI.Release075.AngleDiskCounts
open scoped BigOperators
variable (D : AngleDiskCounts)

theorem OAI.Release075.AngleDiskCounts.linear_face_bound
    (hinterior : ∀ v, D.visits v = 0 → 12 ≤ D.angles v) :
    D.faces + 12 ≤ 6*D.boundaryLength := by sorry
