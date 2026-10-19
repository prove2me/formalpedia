-- Prove2me | Theorems.Thm_OAI_Release075_AngleDiskCounts_cannot_have_geodesic_boundary
-- name    : OAI.Release075.AngleDiskCounts.cannot_have_geodesic_boundary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:02:45.486985+00:00
-- url     : https://prove2.me/theorems/c4516f71-7421-4127-b2ba-078560993ca5
-- title:
--   Curvature forbids a disk with large angles everywhere
-- statement:
--   Angle disk counts consist of finitely many vertices with boundary visits $\mathrm{vis}(v)\in\mathbb N$ and angles $\theta(v)\ge0$, together with numbers $E$ of edges and $F$ of faces, satisfying $|V|+F=E+1$, $\sum_v\mathrm{vis}(v)+3F=2E$ and $\sum_v\theta(v)=5F$. The curvature is $\kappa(v)=10-5\,\mathrm{vis}(v)-\theta(v)$ (so $10$ stands for a full turn), and the boundary length is $\sum_v\mathrm{vis}(v)$. It is impossible that every interior vertex ($\mathrm{vis}=0$) has angle $\ge10$ and every vertex visited once by the boundary has angle $\ge5$:
--   $$
--   \sum_v\kappa(v)=10>0 .
--   $$
--
--   This is the combinatorial Gauss–Bonnet obstruction to a disk whose boundary turns by at least $\pi$ everywhere.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Ribbons.lean#L37-L58

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

theorem OAI.Release075.AngleDiskCounts.cannot_have_geodesic_boundary
    (hinterior : ∀ v, D.visits v = 0 → 10 ≤ D.angles v)
    (hboundary : ∀ v, D.visits v = 1 → 5 ≤ D.angles v) : False := by sorry
