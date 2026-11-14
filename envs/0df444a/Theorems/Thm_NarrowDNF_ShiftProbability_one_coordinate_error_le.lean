-- Prove2me | Theorems.Thm_NarrowDNF_ShiftProbability_one_coordinate_error_le
-- name    : NarrowDNF.ShiftProbability.one_coordinate_error_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:23:37.155193+00:00
-- url     : https://prove2.me/theorems/11e13899-988c-42a9-90b6-5cac00897f22
-- title:
--   A bias-matched random coordinate shift does not increase approximation error
-- statement:
--   Let $I$ be finite, $0\le p\le1$, $i\in I$, and let $f,v:\{0,1\}^I\to\{0,1\}$, with $f$ monotone. Write $e_p(f,v)=\Pr_p(f\ne v)$. Define $U_iv(x)=v(x)\lor v(x^{i,0})$ and $L_iv(x)=v(x)\land v(x^{i,1})$. Then
--   $$
--   (1-p)e_p(f,U_iv)+p\,e_p(f,L_iv)\le e_p(f,v).
--   $$
--   Thus an independent random choice of upper shift with weight $1-p$ and lower shift with weight $p$ preserves the error budget in expectation. No monotonicity of the approximator $v$ is assumed.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ShiftProbability.lean#L54-L71

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_FiberShift
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

namespace NarrowDNF.ShiftProbability
end NarrowDNF.ShiftProbability
noncomputable section
open NarrowDNF
open NarrowDNF.ShiftProbability
open ProductMeasure
variable {ι : Type*} [DecidableEq ι]
variable [Fintype ι]

theorem NarrowDNF.ShiftProbability.one_coordinate_error_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : ι) (f v : Cube ι → Bool) (hf : Monotone f) :
    (1-p) * ProductMeasure.error p f (upperShift i v) +
        p * ProductMeasure.error p f (lowerShift i v) ≤ ProductMeasure.error p f v := by sorry
