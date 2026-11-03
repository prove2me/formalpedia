-- Prove2me | Theorems.Thm_LX_AffineScan_reflection_opposite_pairs
-- name    : LX.AffineScan.reflection_opposite_pairs
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:04:43.283889+00:00
-- url     : https://prove2.me/theorems/a662f62f-f83d-491f-9295-c65e4ebb38c4
-- title:
--   Reflection crossings with opposite winding parity
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For an integer board $d:I_n\to\mathbb Z$, put $F_i=i+d_i$, $\lambda_i=F_i\bmod n$, $C_{ij}=-\lfloor(((j-i)\bmod n)+d_j-d_i)/n\rfloor$, $B_i=\sum_j\max(-C_{ij},0)$, and $I(d)=\sum_{i<j}|\lfloor(F_j-F_i)/n\rfloor|$. Let $n>0$, let $\rho$ permute $I_n$, and assume $F_i=C-\rho(i)+nk_i$ for an integer $C$ and integers $k_i$. Color $i$ by the parity of $k_i$. Let $S$ count pairs $i<j$ of equal color and $O$ count inversions of $\rho$ with opposite colors. Then
--
--   $$
--   S+2O\le I(d)+\operatorname{inv}(\rho).
--   $$
--
--   Keeping the opposite-color inverted pairs sharpens the reflection lower estimate.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/ColoredReflectionLower.lean#L12-L71

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
import Definitions.Def_LX_ColoredReflectionLower
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_TwoColorPairs
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.Antipode
end LX.Antipode
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.WordReflection
end LX.Core.WordReflection
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem LX.AffineScan.reflection_opposite_pairs (d : Fin n → ℤ) (ρ : State n)
    (C : ℤ) (k : Fin n → ℤ)
    (hF : ∀ i,targets d i=C-(ρ i : ℤ)+(n : ℤ)*k i) :
    sameColorPairs (fun i => decide (k i % 2=0))+
      2*oppositeColorInversions ρ (fun i => decide (k i % 2=0)) ≤
        inversions d+LX.Core.FiniteCuts.inversionNumber ρ := by sorry
