-- Prove2me | Theorems.Thm_LX_FinitePairReduction_position_run_partner_bound
-- name    : LX.FinitePairReduction.position_run_partner_bound
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:02:21.37628+00:00
-- url     : https://prove2.me/theorems/8e6d4688-1522-4f0a-9784-44d7cea5d174
-- title:
--   A token's absolute lifted displacement is bounded by the number of its recorded partners
-- statement:
--   A token's absolute lifted displacement is bounded by the number of its recorded partners.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. A lifted configuration additionally records an integer position for each token and an integer cursor. The lifted run iterates these steps in word order. The visible permutation is the physical token arrangement viewed from its cursor. The partner list records every token exchanged with the specified token during the word, with multiplicity.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (w : \operatorname{Seq} \mathcal A) (s : \operatorname{Conf} n) (i : I_{n}), |(\operatorname{LRun} (\operatorname{map} \operatorname{inc} w) s)_{\rm pos} i - s_{\rm pos} i| \le  \operatorname{rep}\,(\operatorname{Partners} i w (\operatorname{Vis} s))_{\ell}
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ShortestLiftRange.lean#L23-L50

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
import Definitions.Def_LX_FinitePairReduction
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedScanBridge
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.FinitePairReduction
end LX.FinitePairReduction
namespace LX.LiftedScan
end LX.LiftedScan
namespace List
end List

namespace LX.FinitePairReduction
end LX.FinitePairReduction
open LX
open LX.FinitePairReduction
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]

theorem LX.FinitePairReduction.position_run_partner_bound (w : List Letter) (s : Configuration n) (i : Fin n) :
    |(run (w.map Letter.toCore) s).position i-s.position i| ≤
      ((partners i w (LiftedScan.visible s)).length : ℤ) := by sorry
