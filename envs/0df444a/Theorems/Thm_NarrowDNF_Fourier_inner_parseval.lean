-- Prove2me | Theorems.Thm_NarrowDNF_Fourier_inner_parseval
-- name    : NarrowDNF.Fourier.inner_parseval
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:23:56.942292+00:00
-- url     : https://prove2.me/theorems/9e9b58c2-e71a-46b1-83a0-20a8384eee06
-- title:
--   The inner-product Parseval identity for the biased Boolean cube
-- statement:
--   Let \(I\) be finite, \(0<p<1\), and \(f,g:\{0,1\}^I\to\mathbb R\). For the normalized characters \(\chi_S^p(x)=\prod_{i\in S}\frac{x_i-p}{\sqrt{p(1-p)}}\), define \(\widehat f_p(S)=\mathbb E_p[f\chi_S^p]\) and similarly for \(g\). Then
--   $$\mathbb E_p[fg]=\sum_{S\subseteq I}\widehat f_p(S)\widehat g_p(S).$$
--   This identifies the product-measure inner product with the Euclidean inner product of the Fourier coefficient arrays. Taking \(g=f\) gives the usual equality between the second moment and the sum of squared coefficients.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L117-L142

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_Fourier_expansion

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.Fourier
section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.Fourier.inner_parseval {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f g : (ι → Bool) → ℝ) :
    ProductMeasure.expectation p (fun x => f x * g x) =
      ∑ s : ι → Bool, coefficient p f s * coefficient p g s := by sorry
