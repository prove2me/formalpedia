-- Prove2me | Theorems.Thm_LX_CycleGeometry_single_three_consecutive_at_zero
-- name    : LX.CycleGeometry.single_three_consecutive_at_zero
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:22:42.175312+00:00
-- url     : https://prove2.me/theorems/c8a1291b-15ec-49c9-996f-8de50bd8c523
-- title:
--   A zero-defect permutation with one unit of cycle-size excess has one consecutive forward three-cycle
-- statement:
--   A zero-defect permutation with one unit of cycle-size excess has one consecutive forward three-cycle.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. $\mathcal P_{\rm fin}(X)$ denotes finite subsets and a subscript $\#$ denotes cardinality. Function symbols are written in curried notation. $\mathrm{Def}(p)=\sum_i|\Delta(p,i)|-\operatorname{inv}(p)-|\operatorname{supp}(p)|+|\operatorname{cycles}(p)|$ is cycle defect. $\operatorname{supp}(p)$ is the moved-point set and $\operatorname{cycles}(p)$ its nontrivial disjoint cycle factors; cycle membership includes fixed singleton orbits.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (q : \mathfrak S(I_n)), \operatorname{Def} q = 0 \to  (\operatorname{supp} q)_{\#} = 2\, (\operatorname{cycles} q)_{\#} + 1 \to  (\forall  (i : I_{n}), q i = i \to  i = 0) \to  (\forall  (i j : I_{n}), \operatorname{rep}\,i + 1 = \operatorname{rep}\,j \to  q j \ne  i) \to  \exists  a b c, \operatorname{rep}\,a + 1 = \operatorname{rep}\,b \land  \operatorname{rep}\,b + 1 = \operatorname{rep}\,c \land  q a = b \land  q b = c \land  q c = a \land  \forall  (i : I_{n}), i \ne  a \to  i \ne  b \to  i \ne  c \to  q (q i) = i
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/SingleThreeGeometry.lean#L56-L138

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
import Definitions.Def_LX_TwoWindowCycleDefect
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.AnchoredPhases
end LX.AnchoredPhases
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
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.CycleGeometry
end LX.CycleGeometry
namespace LX.EventGeometry
end LX.EventGeometry
namespace LX.FiniteJoin
end LX.FiniteJoin
namespace LX.PairCore
end LX.PairCore
namespace List
end List

namespace LX.CycleGeometry
end LX.CycleGeometry
open LX
open LX.CycleGeometry
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem LX.CycleGeometry.single_three_consecutive_at_zero (q : State n) (hq : cycleDefect q=0)
    (he : q.support.card=2*q.cycleFactorsFinset.card+1)
    (hfixed : ∀ i : Fin n,q i=i → i=0)
    (hback : ∀ i j : Fin n,i.val+1=j.val → q j ≠ i) :
    ∃ a b c : Fin n,a.val+1=b.val ∧ b.val+1=c.val ∧
      q a=b ∧ q b=c ∧ q c=a ∧
      ∀ i : Fin n,i ≠ a → i ≠ b → i ≠ c → q (q i)=i := by sorry
