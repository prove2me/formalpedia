-- Prove2me | Theorems.Thm_LX_Core_AffineLift_majorized_level_count
-- name    : LX.Core.AffineLift.majorized_level_count
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T18:59:36.755204+00:00
-- url     : https://prove2.me/theorems/ce36bd2b-1f6b-4e4c-962c-301237dd01f4
-- title:
--   A majorized vector has at most n minus twice h coordinates equal to h
-- statement:
--   Let $n$ be a natural number and let $d:\{0,\ldots,n-1\}\to\mathbb Z$ satisfy subset majorization: for every subset $S$,
--   $2\sum_{i\in S}d(i)\le |S|(n-|S|)$. For any integer $h$ with $2h\le n$, its level multiplicity satisfies
--
--   $$
--   \bigl|\{i:d(i)=h\}\bigr|\le n-2h.
--   $$
--
--   Neither balancedness of $d$ nor positivity of $h$ is assumed. The dimension may be zero. The estimate bounds repeated extreme coordinates, allowing majorization to impose restrictions on the number of matching pairs sharing an extreme displacement.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/MajorizedExtremeCount.lean#L8-L24

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
import Definitions.Def_LX_AffineLift

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
namespace List
end List

namespace LX.Core.AffineLift
end LX.Core.AffineLift
open LX
open LX.Core
open LX.Core.AffineLift
open scoped BigOperators
variable {n : ℕ}

theorem LX.Core.AffineLift.majorized_level_count {d : Fin n → ℤ} (hm : Majorized d) (h : ℤ)
    (hh : 2*h ≤ (n : ℤ)) :
    ((Finset.univ.filter (fun i => d i=h)).card : ℤ) ≤ (n : ℤ)-2*h := by sorry
