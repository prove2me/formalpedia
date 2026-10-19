-- Prove2me | Theorems.Thm_OAI_Release075_MarkedLineData_presentation_wordHyperbolic
-- name    : OAI.Release075.MarkedLineData.presentation_wordHyperbolic
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T08:37:34.828985+00:00
-- url     : https://prove2.me/theorems/65f0b86b-8d27-499b-be0e-bdcef10b7634
-- title:
--   The marked-line presentation is word hyperbolic
-- statement:
--   Let $d$ be marked-line data over a prime $q$ with parameter $r>0$ and let $\Gamma$ be the presented group of its block presentation. Then $\Gamma$ is word hyperbolic in the thin-triangle sense. The finite generating set $S$ of generator images has connected Cayley graph, and with
--   $$
--   \delta=10000\cdot115,
--   $$
--   every vertex of a side of a geodesic triangle in the Cayley graph is within distance $\delta$ of one of the other two sides.
--
--   This is the hyperbolicity part of the main theorem.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Hyperbolicity.lean#L17-L49

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
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CayleyPaths

open OAI OAI.Release075 OAI.Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem OAI.Release075.MarkedLineData.presentation_wordHyperbolic : WordHyperbolic (d.presentation hr).GroupType := by sorry
