-- Prove2me | Theorems.Thm_OAI_Release075_TriangleFilling_edge_sum_bound
-- name    : OAI.Release075.TriangleFilling.edge_sum_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T08:35:52.49411+00:00
-- url     : https://prove2.me/theorems/ae82d9cf-3bf0-4a9a-8f08-c3882e6d7180
-- title:
--   Bounded face coboundary bounds boundary sums by the filling size
-- statement:
--   Let $D$ be a triangle filling of a word $w$ over an edge alphabet with flip and face relation. Let $F:E\to\mathbb Z$ be antisymmetric, $F(\mathrm{flip}\,e)=-F(e)$, with bounded coboundary on faces:
--   $$
--   |F(a)+F(b)+F(c)|\le2\quad\text{whenever }\mathrm{face}(a,b,c).
--   $$
--   Then
--   $$
--   \Bigl|\sum_{e\in w}F(e)\Bigr|\le2\,\mathrm{active}(D).
--   $$
--
--   Applied to the lifted tent form, it turns the linear filling estimate into a linear cochain bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/CayleyMetric.lean#L100-L124

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
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullChains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_BasedWords
import Definitions.Def_OAI_GroupTheory_Hyperbolic_DiscreteMetric
import Definitions.Def_OAI_GroupTheory_Hyperbolic_ThinTriangles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CayleyMetric

open OAI OAI.Release075 OAI.Release075.TriangleFilling
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem OAI.Release075.TriangleFilling.edge_sum_bound {w : List E} (D : TriangleFilling flip color face w)
    (F : E → ℤ) (hflip : ∀ e, F (flip e) = -F e)
    (hface : ∀ a b c, face a b c → |F a+F b+F c| ≤ 2) :
    |(w.map F).sum| ≤ 2*D.activeCount := by sorry
