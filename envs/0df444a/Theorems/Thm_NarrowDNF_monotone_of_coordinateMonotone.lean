-- Prove2me | Theorems.Thm_NarrowDNF_monotone_of_coordinateMonotone
-- name    : NarrowDNF.monotone_of_coordinateMonotone
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:16:12.687027+00:00
-- url     : https://prove2.me/theorems/85fa334a-b7b4-4a01-8b8e-ea2015db21e0
-- title:
--   Coordinatewise monotonicity implies monotonicity on a finite Boolean cube
-- statement:
--   Let $I$ be finite and $v:\{0,1\}^I\to\{0,1\}$. Assume every coordinate fiber is nondecreasing: for every $i\in I$ and every assignment of the remaining coordinates, the value with bit zero is at most the value with bit one. Then
--   $$
--   x\le y\ \text{coordinatewise}\quad\Longrightarrow\quad v(x)\le v(y).
--   $$
--   This includes an empty coordinate set. It is the step that turns the coordinate monotonicity established by repeated shifts into the ordinary monotonicity required for positive certificates.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/CoordinateShift.lean#L126-L155

import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_CoordinateShift

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift
open NarrowDNF
variable {ι : Type*} [DecidableEq ι]

theorem NarrowDNF.monotone_of_coordinateMonotone [Fintype ι] {v : Cube ι → Bool}
    (hv : ∀ i, CoordinateMonotone i v) : Monotone v := by sorry
