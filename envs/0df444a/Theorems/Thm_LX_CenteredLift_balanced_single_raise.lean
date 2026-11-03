-- Prove2me | Theorems.Thm_LX_CenteredLift_balanced_single_raise
-- name    : LX.CenteredLift.balanced_single_raise
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:04:07.831205+00:00
-- url     : https://prove2.me/theorems/53891c17-ebeb-4d94-95cf-493a8281e6be
-- title:
--   At most one coordinate is raised by a period
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. Let $n>0$, $m\in\mathbb N$, and $d,e:I_n\to\mathbb Z$. Assume $\sum_i d_i=0$, $d_i\ge-m$, $-m\le e_i<n-m$, $d_i\equiv e_i\pmod n$, and $\sum_i e_i\ge-n$. Then
--
--   $$
--   d=e\quad\text{or}\quad\exists a:\ d_i=e_i+n\mathbf1_{i=a}\ \text{for all }i.
--   $$
--
--   A strip representative of sufficiently large mass differs from a balanced lift by at most one full-period correction.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/CenteredLiftSelection.lean#L67-L113

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
import Definitions.Def_LX_CenteredLiftSelection

namespace Int
end Int
namespace LX
end LX
namespace LX.CenteredLift
end LX.CenteredLift
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace List
end List

namespace LX.CenteredLift
end LX.CenteredLift
open LX
open LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.CenteredLift.balanced_single_raise (m : ℕ) (d e : Fin n → ℤ)
    (hd : ∑ i,d i=0) (hlo : ∀ i,-(m : ℤ) ≤ d i)
    (he : ∀ i,-(m : ℤ) ≤ e i ∧ e i < (n : ℤ)-m)
    (hres : ∀ i,(d i : Fin n)=(e i : Fin n))
    (hs : -(n : ℤ) ≤ ∑ i,e i) : d=e ∨ ∃ a,d=raiseAt e a := by sorry
