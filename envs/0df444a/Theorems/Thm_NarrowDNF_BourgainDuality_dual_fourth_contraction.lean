-- Prove2me | Theorems.Thm_NarrowDNF_BourgainDuality_dual_fourth_contraction
-- name    : NarrowDNF.BourgainDuality.dual_fourth_contraction
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:18:46.430698+00:00
-- url     : https://prove2.me/theorems/767ea2ed-5d49-4b3f-9f2c-d36515ee8a64
-- title:
--   Dual fourth-moment contraction for a self-adjoint map
-- statement:
--   Let \(\alpha\) be finite, let \(w_x\ge0\), and let \(T\) map real functions on \(\alpha\) to real functions. Assume weighted self-adjointness, \(\sum_xw_x(Ta)_xb_x=\sum_xw_xa_x(Tb)_x\) for all functions \(a,b\). Suppose also that \(T\) contracts fourth moments: \(\sum_xw_x(Ta)_x^4\le\sum_xw_xa_x^4\) for every \(a\). Then every real function \(f\) satisfies
--   $$\sum_xw_x|(Tf)_x|^{4/3}\le\sum_xw_x|f_x|^{4/3}.$$
--   Thus fourth-moment contraction transfers to the conjugate exponent \(4/3\), for arbitrary nonnegative finite weights.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainDuality.lean#L102-L129

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

theorem NarrowDNF.BourgainDuality.dual_fourth_contraction (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (T : (α → ℝ) → α → ℝ)
    (hself : ∀ f g, (∑ x, w x * T f x * g x) = ∑ x, w x * f x * T g x)
    (hfourth : ∀ f, (∑ x, w x * T f x ^ 4) ≤ ∑ x, w x * f x ^ 4)
    (f : α → ℝ) : moment43 w (T f) ≤ moment43 w f := by sorry
