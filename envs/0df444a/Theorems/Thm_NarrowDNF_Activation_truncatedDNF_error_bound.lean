-- Prove2me | Theorems.Thm_NarrowDNF_Activation_truncatedDNF_error_bound
-- name    : NarrowDNF.Activation.truncatedDNF_error_bound
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:18:47.190504+00:00
-- url     : https://prove2.me/theorems/9e2c188a-5a9b-47c4-86ef-7c72a296c8a9
-- title:
--   Weighted error bound for a truncated certificate DNF
-- statement:
--   Let \(\iota\) be finite, let \(J\) be an increasing local activation family, and let \(u:\{0,1\}^{\iota}\to\{0,1\}\) be monotone and determined by its adaptive atom. Define the active union \(A(x)\) and its positive certificate \(C(x)=\{i\in A(x):x_i=1\}\). For \(w\in\mathbb N\), let \(v_w\) be the monotone DNF whose terms are exactly the certificates \(C(z)\) with \(u(z)=1\) and \(|C(z)|\le w\). For every nonnegative weighting \(a:\{0,1\}^{\iota}\to\mathbb R\),
--   $$\sum_x a(x)\mathbf1_{u(x)\ne v_w(x)}\le\sum_x a(x)\mathbf1_{|C(x)|>w}\le\frac{\sum_x a(x)|A(x)|}{w+1}.$$
--   This gives a width-dependent approximation bound without requiring normalized weights.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/CertificateBounds.lean#L50-L72

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_CertificateBounds
import Definitions.Def_NarrowDNF_Certificates
import Theorems.Thm_NarrowDNF_Activation_positive_certificate
import Theorems.Thm_NarrowDNF_Weighted_integer_markov

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation
open NarrowDNF
open NarrowDNF
open NarrowDNF.Activation
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.Activation.truncatedDNF_error_bound {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u) (w : ℕ)
    (weights : Cube ι → ℝ) (hw : ∀ x, 0 ≤ weights x) :
    (∑ x, weights x * (if u x ≠ J.truncatedDNF u w x then 1 else 0)) ≤
      (∑ x, weights x * (if w < (J.certificate x).card then 1 else 0)) ∧
    (∑ x, weights x * (if w < (J.certificate x).card then 1 else 0)) ≤
      (∑ x, weights x * ((J.activeFinset x).card : ℝ)) / (w + 1 : ℝ) := by sorry
