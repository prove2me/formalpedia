-- Prove2me | Theorems.Thm_NarrowDNF_BourgainDuality_dual_contract24
-- name    : NarrowDNF.BourgainDuality.dual_contract24
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:18:25.690208+00:00
-- url     : https://prove2.me/theorems/f8b20447-7f0c-419e-80cc-b398f50eeebb
-- title:
--   Dual form of a weighted L2-to-L4 contraction
-- statement:
--   Let \(\alpha\) be finite, let \(w_x\ge0\) be weights, and let \(T\) map real functions on \(\alpha\) to real functions. Assume weighted self-adjointness, \(\sum_xw_x(Ta)_xb_x=\sum_xw_xa_x(Tb)_x\) for all \(a,b\), and the bound \(\sum_xw_x(Ta)_x^4\le(\sum_xw_xa_x^2)^2\) for all \(a\). Define \(m_{4/3}(f)=\sum_xw_x|f_x|^{4/3}\). Every real function \(f\) then satisfies
--   $$\left(\sum_xw_x(Tf)_x^2\right)^2\le m_{4/3}(f)^3.$$
--   This is the weighted \(L^{4/3}\)-to-\(L^2\) dual estimate. The weights need not sum to one. No separate linearity assumption on the map is needed.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainDuality.lean#L131-L153

import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_NarrowDNF_BourgainDuality
import Theorems.Thm_NarrowDNF_BourgainDuality_weighted_holder43

namespace NarrowDNF.BourgainDuality
end NarrowDNF.BourgainDuality
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainDuality
variable {α : Type*} [Fintype α]

theorem NarrowDNF.BourgainDuality.dual_contract24 (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (T : (α → ℝ) → α → ℝ)
    (hself : ∀ f g, (∑ x, w x * T f x * g x) = ∑ x, w x * f x * T g x)
    (h24 : ∀ f, (∑ x, w x * T f x ^ 4) ≤ (∑ x, w x * f x ^ 2)^2)
    (f : α → ℝ) :
    (∑ x, w x * T f x ^ 2)^2 ≤ moment43 w f ^ 3 := by sorry
