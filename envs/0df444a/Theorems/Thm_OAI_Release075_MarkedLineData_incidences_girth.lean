-- Prove2me | Theorems.Thm_OAI_Release075_MarkedLineData_incidences_girth
-- name    : OAI.Release075.MarkedLineData.incidences_girth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:49:46.242984+00:00
-- url     : https://prove2.me/theorems/f1e3b271-debd-4b19-ae9e-34dfdcb6bf14
-- title:
--   The incidence graph of marked-line data has girth at least fourteen
-- statement:
--   Let $d$ be marked-line data over a prime $q$, and consider the bipartite graph between labels and points of $\mathbb F_q^{20}$ in which $i$ is joined to $z$ when $z$ lies on the punctured line of $i$. Every cycle $p$ in this graph has
--   $$
--   \mathrm{length}(p)\ge14 .
--   $$
--
--   This girth feeds the girth of the vertex links of the triangle complex.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Presentation.lean#L520-L534

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation

open OAI OAI.Release075 OAI.Release075.MarkedLineData
open scoped BigOperators
attribute [local instance] OAI.Release075.instDecidableEq_oAI
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

theorem OAI.Release075.MarkedLineData.incidences_girth (a : d.Label ⊕ (Fin 20 → ZMod q))
    (p : (relationGraph (fun i z => i ∈ d.incidences z)).Walk a a) (hp : p.IsCycle) :
    14 ≤ p.length := by sorry
