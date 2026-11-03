-- Prove2me | Theorems.Thm_LX_Core_ZeroGap_select_event_edges
-- name    : LX.Core.ZeroGap.select_event_edges
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:19:15.398218+00:00
-- url     : https://prove2.me/theorems/83d9602c-cb36-48e2-8219-52f408c98ec8
-- title:
--   Any subset of event edge keys can be represented by an ordered sublist without duplicate keys
-- statement:
--   Any subset of event edge keys can be represented by an ordered sublist without duplicate keys.
--
--   Let $n$ be a natural number and let $I_n=\{0,\ldots,n-1\}$; this set may be empty. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. Variables named events or part denote event lists; untyped vertex variables range over $I_n$. Pairwise separation refers to earlier and later entries in their list order. An event $e=(e_1,e_2)$ is an ordered pair of residue positions. $\operatorname{edge}(e)=\{e_1,e_2\}$ is its unordered endpoint key.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N) (events : \operatorname{Seq} (\mathcal E n)), \forall  T \subseteq  (\operatorname{map} \operatorname{edge} events)_{\rm set}, \exists  part, part\mathrel{\preccurlyeq} events \land  (\operatorname{map} \operatorname{edge} part)_{\rm distinct} \land  (\operatorname{map} \operatorname{edge} part)_{\rm set} = T \land  part_{\ell} = T_{\#}
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/SelectedEventEdges.lean#L9-L28

/-
Adapted from https://github.com/snow-ghost/glushkov-lx-lean at 8cddcd222b591673dc63475d9d45b9ed5c6eb92c.
MIT License

Copyright (c) 2026 S. Uskov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
import Mathlib
import Definitions.Def_LX_SelectedEventEdges
import Definitions.Def_LX_ZeroGapEventGeometry

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ}

theorem LX.Core.ZeroGap.select_event_edges (events : List (Event n)) (T : Finset (Sym2 (Fin n)))
    (hT : T ⊆ (events.map eventEdgeKey).toFinset) :
    ∃ part : List (Event n), part.Sublist events ∧
      (part.map eventEdgeKey).Nodup ∧ (part.map eventEdgeKey).toFinset=T ∧ part.length=T.card := by sorry
