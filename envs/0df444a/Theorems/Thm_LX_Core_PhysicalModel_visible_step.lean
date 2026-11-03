-- Prove2me | Theorems.Thm_LX_Core_PhysicalModel_visible_step
-- name    : LX.Core.PhysicalModel.visible_step
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:57:06.639731+00:00
-- url     : https://prove2.me/theorems/45672f30-eeb3-4494-872b-a69bea49a44f
-- title:
--   A physical generator step multiplies the visible permutation by that generator
-- statement:
--   A physical generator step multiplies the visible permutation by that generator.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. A physical configuration consists of a token permutation and a residue cursor. The visible permutation is the physical token arrangement viewed from its cursor. A physical step updates the cursor for rotation letters and swaps the two cursor-neighbor tokens for exchange. The symmetric alphabet $\mathcal A_{\pm}$ contains forward rotation, inverse rotation and adjacent exchange; inverse letters reverse the two rotation letters and fix exchange.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (a : \mathcal A_{\pm}) (s : \operatorname{Phys} n), \operatorname{Vis} (\operatorname{Step} a s) = \operatorname{Vis} s\, a_{\rm ev}
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/PhysicalModel.lean#L29-L49

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel

namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel

namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
open LX
open LX.Core
open LX.Core.PhysicalModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.Core.PhysicalModel.visible_step (a : Letter) (s : Configuration n) :
    visible (step a s) = visible s * a.eval (n := n) := by sorry
