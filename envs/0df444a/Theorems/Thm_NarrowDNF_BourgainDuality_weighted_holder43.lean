-- Prove2me | Theorems.Thm_NarrowDNF_BourgainDuality_weighted_holder43
-- name    : NarrowDNF.BourgainDuality.weighted_holder43
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:03:45.902905+00:00
-- url     : https://prove2.me/theorems/17c1c180-6619-4422-9a4c-3df27dc98bac
-- title:
--   Weighted Hölder inequality with exponents 4/3 and 4
-- statement:
--   Let \(\alpha\) be a finite set, let \(w:\alpha\to\mathbb R\) have nonnegative values, and let \(f,g:\alpha\to\mathbb R\) be arbitrary real functions. Define \(m_{4/3}(f)=\sum_xw_x|f_x|^{4/3}\). The weighted pairing satisfies
--   $$\left|\sum_xw_xf_xg_x\right|\le m_{4/3}(f)^{3/4}\left(\sum_xw_xg_x^4\right)^{1/4}.$$
--   Zero weights are allowed and normalization is unnecessary. This is the conjugate-exponent inequality needed to transfer self-adjoint fourth-moment contraction to estimates at exponent \(4/3\).
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainDuality.lean#L24-L61

import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_NarrowDNF_BourgainDuality

namespace NarrowDNF.BourgainDuality
end NarrowDNF.BourgainDuality
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainDuality
variable {α : Type*} [Fintype α]

theorem NarrowDNF.BourgainDuality.weighted_holder43 (w f g : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    |∑ x, w x * f x * g x| ≤
      moment43 w f ^ (3/4 : ℝ) * (∑ x, w x * g x ^ 4) ^ (1/4 : ℝ) := by sorry
