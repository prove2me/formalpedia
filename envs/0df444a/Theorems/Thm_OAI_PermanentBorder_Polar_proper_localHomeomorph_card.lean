-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Polar_proper_localHomeomorph_card
-- name    : OAI.PermanentBorder.Polar.proper_localHomeomorph_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:50:23.113702+00:00
-- url     : https://prove2.me/theorems/99316c79-9c5b-4c71-8ac0-6e5b22d11fef
-- title:
--   Fibres of a proper local homeomorphism over a preconnected space all have the same cardinality
-- statement:
--   Let $X$ and $Y$ be topological spaces such that $X$ is Hausdorff and $Y$ is preconnected (it is not the union of two disjoint nonempty open sets). Let $f:X\to Y$ be a proper map, that is, continuous, closed and with compact fibres, which is also a local homeomorphism: every point of $X$ has an open neighbourhood that $f$ maps homeomorphically onto an open subset of $Y$. Then all fibres of $f$ have the same number of points: for all $y,z\in Y$,
--
--   $$
--   \#f^{-1}(y)=\#f^{-1}(z).
--   $$
--
--   In applications $X$ is the set of solutions of a family of equation systems, $Y$ is a connected parameter space and $f$ is the projection to the parameter. Properness says that no solution escapes to infinity, and the local homeomorphism property holds when all solutions are nondegenerate. The theorem then says that the number of solutions does not depend on the parameter, which is the topological core of counting roots by continuation.
--
--   **Formalization Note** Properness is Mathlib's `IsProperMap`, which is equivalent to being continuous and closed with compact fibres; the local homeomorphism property is `IsLocalHomeomorph`; the number of points is `Nat.card`, which assigns $0$ to infinite sets. Under the hypotheses every fibre is compact and discrete, hence finite, so this convention plays no role.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/RegularSections.lean#L361-L375

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections

open OAI OAI.PermanentBorder OAI.PermanentBorder.Polar
open Topology Filter
open scoped Topology

theorem OAI.PermanentBorder.Polar.proper_localHomeomorph_card {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] [PreconnectedSpace Y] {f : X → Y}
    (hp : IsProperMap f) (hl : IsLocalHomeomorph f) (y z : Y) :
    Nat.card (f ⁻¹' {y}) = Nat.card (f ⁻¹' {z}) := by sorry
