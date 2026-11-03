-- Prove2me | Theorems.Thm_LX_Core_FiniteCuts_rotation_energy_change
-- name    : LX.Core.FiniteCuts.rotation_energy_change
-- status  : Proved
-- author  : @chaos-ghost
-- created : 2026-11-02T19:18:47.845633+00:00
-- url     : https://prove2.me/theorems/80757279-252c-4cfd-b099-4a4b7b2ed314
-- title:
--   Change of displacement mass under rotating the cut
-- statement:
--   Write $I_n=\{0,\ldots,n-1\}$, with cyclic arithmetic modulo $n$ and integer representatives for inequalities; $[x]_n$ denotes the least nonnegative residue when $n>0$. For a permutation $p$, write $d(p)=|\{i:p(i)<i\}|$, $u(p)=|\{i:p(i)+1=i\}|$, $M(p)=\sum_i|p(i)-i|$, and $J(p)=\operatorname{inv}(p)$; all comparisons use integer representatives. Let $n=k+1$ and $A(i)=i+1\pmod n$. Set $q=A^{-1}pA$. Then
--
--   $$
--   M(q)-M(p)=\begin{cases}0,&p(0)=0,\\2n-2p(0)-2p^{-1}(0),&p(0)\ne0.\end{cases}
--   $$
--
--   The mass change depends only on the arrows incident to the moved cut.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/FiniteEnergyRotation.lean#L63-L91

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
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteEnergyRotation
import Definitions.Def_LX_Graph

namespace Int
end Int
namespace LX
end LX
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
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace List
end List

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open scoped BigOperators
variable {k : ℕ}

theorem LX.Core.FiniteCuts.rotation_energy_change (p : State (k+1)) :
    (∑ i : Fin (k+1), |_root_.LX.Core.FiniteCuts.displacement (rotateConjugate p) i|)-
      (∑ i : Fin (k+1), |_root_.LX.Core.FiniteCuts.displacement p i|)=
      if p 0=0 then 0 else 2*(k+1 : ℤ)-2*(p 0 : ℤ)-2*(p.symm 0 : ℤ) := by sorry
