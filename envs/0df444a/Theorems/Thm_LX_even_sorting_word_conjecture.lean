-- Prove2me | Theorems.Thm_LX_even_sorting_word_conjecture
-- name    : LX.even_sorting_word_conjecture
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:27:07.33911+00:00
-- url     : https://prove2.me/theorems/8a2d6eec-d1ce-426a-89e1-608836c8e540
-- title:
--   Sharp sorting-word bound in even size
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Words use a forward cyclic rotation $L$ and the exchange $X=(0\ 1)$; $\operatorname{ev}(w)$ is their permutation product and $|w|$ their number of letters. Let $n\ge4$, $m\in\mathbb N$, and $n=2m$. For every permutation $p$ of $I_n$,
--
--   $$
--   \exists w:\quad p\operatorname{ev}(w)=1,\quad4|w|\le3n^2-8n+12.
--   $$
--
--   This proves the even parity sorting threshold for all permutations.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/EvenConjecture.lean#L10-L37

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
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.AnchoredPhases
end LX.AnchoredPhases
namespace LX.Antipode
end LX.Antipode
namespace LX.CenteredLift
end LX.CenteredLift
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCoordinates
end LX.Core.FiniteCoordinates
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.FiniteGaps
end LX.Core.FiniteGaps
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.WordReflection
end LX.Core.WordReflection
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.CycleGeometry
end LX.CycleGeometry
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
namespace LX.EventGeometry
end LX.EventGeometry
namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
namespace LX.FiniteJoin
end LX.FiniteJoin
namespace LX.FinitePairReduction
end LX.FinitePairReduction
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.LiftedScan
end LX.LiftedScan
namespace LX.MatchingGeometry
end LX.MatchingGeometry
namespace LX.PairCore
end LX.PairCore
namespace LX.Small4
end LX.Small4
namespace LX.Small5
end LX.Small5
namespace LX.Small6
end LX.Small6
namespace List
end List

namespace LX
end LX
open LX
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.even_sorting_word_conjecture (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by sorry
