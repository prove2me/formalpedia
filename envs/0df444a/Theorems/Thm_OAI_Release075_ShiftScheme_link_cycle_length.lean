-- Prove2me | Theorems.Thm_OAI_Release075_ShiftScheme_link_cycle_length
-- name    : OAI.Release075.ShiftScheme.link_cycle_length
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:48:46.793211+00:00
-- url     : https://prove2.me/theorems/3e56072d-4dcf-4498-b6c6-effbe1be55e0
-- title:
--   The link of a shift scheme inherits the incidence girth
-- statement:
--   A shift scheme over labels $I$, points $P$ with incidence sets $\mathrm{inc}(z)\subseteq I$ and blocks $B$ assigns to each block $b$ a size $\ge r$, a label set inside $\mathrm{inc}(\mathrm{point}(b))$ with coordinates $c_b$, and a point; each label lies in at most one block over a given point. Its link is the bipartite graph joining $(i,u,v)\in I\times[r]^2$ to $(b,u,j)$ iff $i$ lies in block $b$ and $j=c_b(i)+v$. The projection sends $(i,u,v)\mapsto i$ and $(b,u,j)\mapsto\mathrm{point}(b)$ into the label–point incidence graph. If every cycle of the label–point incidence graph has length at least $k$, then every cycle $p$ of the link also satisfies
--   $$
--   \mathrm{length}(p)\ge k .
--   $$
--
--   So link girth is bounded below by incidence girth.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Presentation.lean#L203-L223

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation

open OAI OAI.Release075 OAI.Release075.ShiftScheme
variable {I P B : Type*} {r : ℕ} {inc : P → Finset I} (d : ShiftScheme I P B r inc)

theorem OAI.Release075.ShiftScheme.link_cycle_length (k : ℕ)
    (hgirth : ∀ a (w : (relationGraph (fun i z => i ∈ inc z)).Walk a a),
      w.IsCycle → k ≤ w.length)
    (a : XDirection (I := I) (r := r) ⊕ d.LDirection)
    (p : d.link.Walk a a) (hp : p.IsCycle) : k ≤ p.length := by sorry
