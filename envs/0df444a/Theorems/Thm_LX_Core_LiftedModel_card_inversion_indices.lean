-- Prove2me | Theorems.Thm_LX_Core_LiftedModel_card_inversion_indices
-- name    : LX.Core.LiftedModel.card_inversion_indices
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:01:41.054194+00:00
-- url     : https://prove2.me/theorems/6784cb7e-20d9-404a-84f2-ce688f5faa84
-- title:
--   Cardinality of the periodic inversion-index interval
-- statement:
--   For $q\in\mathbb Z$, define $J(q)=[-q,0)\cap\mathbb Z$ when $q\ge0$, and $J(q)=[0,-q)\cap\mathbb Z$ when $q<0$. Then
--
--   $$
--   |J(q)|=|q|.
--   $$
--
--   The formula includes $q=0$ and converts an interval of periodic inversion copies into its absolute quotient count.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/InversionIndices.lean#L17-L32

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
import Definitions.Def_LX_InversionIndices

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
namespace List
end List

namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
open LX
open LX.Core
open LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]
omit [NeZero n]

theorem LX.Core.LiftedModel.card_inversion_indices (q : ℤ) : (inversionIndices q).card=q.natAbs := by sorry
