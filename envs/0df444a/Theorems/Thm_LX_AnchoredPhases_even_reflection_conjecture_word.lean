-- Prove2me | Theorems.Thm_LX_AnchoredPhases_even_reflection_conjecture_word
-- name    : LX.AnchoredPhases.even_reflection_conjecture_word
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:24:04.826244+00:00
-- url     : https://prove2.me/theorems/dde2dc0e-e1a4-4c08-ab7e-cc4ba4193cd5
-- title:
--   Even cyclic reflections attain the conjectured sorting-word bound
-- statement:
--   Even cyclic reflections attain the conjectured sorting-word bound.
--
--   Let $n>0$ and write $I_n=\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$. The symbol $\operatorname{rep}$ takes a residue to its nonnegative representative and leaves ordinary integers unchanged. Residue sums and differences are cyclic; inequalities use representatives. $\mathfrak S(I_n)$ is the permutation group. Function symbols are written in curried notation; a subscript $\#$ means finite cardinality. An existential $w$ is a finite word in these generators. Natural subtraction is truncated at zero; scalar price expressions and quantities coerced by $\operatorname{rep}$ are read in the integers. The identity permutation is $1$. Words use forward rotation $l:i\mapsto i+1$ and adjacent exchange $x=(0\ 1)$; $\operatorname{ev}(w)$ is their ordered product.
--
--   The precise quantified assertion, with all its hypotheses, is
--
--   $$
--   \forall  (n : \mathbb N_{>0}) (p : \mathfrak S(I_n)) (r : I_{n}), (\forall  (i : I_{n}), p i = r - i) \to  \forall  (m : \mathbb N), n = 2\, m \to  2 \le  m \to  \exists  w, p\, \operatorname{ev} w = 1 \land  4\, \operatorname{rep}\,w_{\ell} \le  3\, \operatorname{rep}\,n ^{2} - 8\, \operatorname{rep}\,n + 12
--   $$
--
--   This result is used to constrain the remaining phases or to construct a sorting word with the stated cost.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ReflectionConjecture.lean#L14-L66

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
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.PairCore
end LX.PairCore
namespace LX.Small4
end LX.Small4
namespace LX.Small6
end LX.Small6
namespace List
end List

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem LX.AnchoredPhases.even_reflection_conjecture_word (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (m : ℕ) (hn : n=2*m) (hm : 2 ≤ m) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by sorry
