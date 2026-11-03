-- Prove2me | Theorems.Thm_LX_AffineScan_ScanTrace_rotations_le_of_compare_zero
-- name    : LX.AffineScan.ScanTrace.rotations_le_of_compare_zero
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:01:58.413645+00:00
-- url     : https://prove2.me/theorems/68354db9-e52c-4cd8-9aa7-d912703e46ba
-- title:
--   If greedy comparison is zero after k sweeps, every scan trace uses at most k rotations
-- statement:
--   If greedy comparison is zero after k sweeps, every scan trace uses at most k rotations.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\operatorname{Seq}(X)$ denotes finite lists, $\mathcal P_{\rm fin}(X)$ finite subsets; subscripts $\ell,\#,\Pi,\mathrm{set}$ denote length, cardinality, ordered product, and underlying set. A distinctness subscript means no repeated entries. Function symbols are written in curried notation. $\mathrm{Scan}(d,w)$ is a legal greedy scan ending at the zero vector: rotate when $d(0)\le d(1)+1$, exchange otherwise. $\mathrm{Sweep}(d,k)$ repeats head comparison followed by rotation $k$ times. $\mathrm{Cmp}(d)$ exchanges the head pair exactly when $d(1)+1<d(0)$, and otherwise leaves $d$ unchanged.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) , 2 \le  n \to  \forall  (d : I_{n} \to  \mathbb Z) (w : \operatorname{Seq} \mathcal A), \operatorname{Scan} d w \to  \forall  (k : \mathbb N), (\forall  (i : I_{n}), \operatorname{Cmp} (\operatorname{Sweep} d k) i = 0) \to  \operatorname{count} l w \le  k
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/SweepCarrier.lean#L131-L171

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
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_SweepCarrier
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
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace List
end List

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.AffineScan.ScanTrace.rotations_le_of_compare_zero (hn : 2 ≤ n) {d : Fin n → ℤ}
    {w : List Letter} (ht : ScanTrace d w) (k : ℕ)
    (hz : ∀ i, compareHead (sweep d k) i = 0) : w.count .l ≤ k := by sorry
