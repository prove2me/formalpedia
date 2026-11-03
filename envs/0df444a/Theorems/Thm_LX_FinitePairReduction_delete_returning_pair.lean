-- Prove2me | Theorems.Thm_LX_FinitePairReduction_delete_returning_pair
-- name    : LX.FinitePairReduction.delete_returning_pair
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:01:38.820418+00:00
-- url     : https://prove2.me/theorems/ba606a56-946f-4517-a9a1-355955d7ce95
-- title:
--   Deleting two exchanges of a returning finite pair
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Words use a forward cyclic rotation $L$ and the exchange $X=(0\ 1)$; $\operatorname{ev}(w)$ is their permutation product and $|w|$ their number of letters. The unordered labels at the head of a visible permutation $q$ are $\{q(0),q(1)\}$. Let $n>0$, let $p$ be a permutation, and let $a,b\in I_n$. Suppose the head pair is $\{a,b\}$ both in $p$ and after executing $Xu$. For any suffix $v$,
--
--   $$
--   p\operatorname{ev}(XuXv)=p\operatorname{ev}(uv).
--   $$
--
--   The intervening word and all rotation letters survive cancellation of two actual pair exchanges.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FinitePairReduction.lean#L43-L58

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
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.FinitePairReduction
end LX.FinitePairReduction
namespace List
end List

namespace LX.FinitePairReduction
end LX.FinitePairReduction
open LX
open LX.FinitePairReduction
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.FinitePairReduction.delete_returning_pair (p : State n) (a b : Fin n) (u v : List Letter)
    (hfirst : HeadPair p a b) (hsecond : HeadPair (p*eval [.x]*eval u) a b) :
    p*eval (.x::(u++(.x::v)))=p*eval (u++v) := by sorry
