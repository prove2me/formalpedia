-- Prove2me | Theorems.Thm_NarrowDNF_Fourier_kernel
-- name    : NarrowDNF.Fourier.kernel
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:13:55.844913+00:00
-- url     : https://prove2.me/theorems/57f75013-312c-4d09-9256-cda74481a89e
-- title:
--   The tensorized reproducing kernel of the biased Fourier basis
-- statement:
--   Let \(I\) be finite, \(0<p<1\), and \(x,y\in\{0,1\}^I\). Write \(w_p(y)=\prod_i p^{y_i}(1-p)^{1-y_i}\), and for every \(S\subseteq I\) define \(\chi_S^p(z)=\prod_{i\in S}\frac{z_i-p}{\sqrt{p(1-p)}}\). Then
--   $$w_p(y)\sum_{S\subseteq I}\chi_S^p(x)\chi_S^p(y)=\mathbf1_{\{x=y\}}.$$
--   The included weight is the mass of \(y\). This kernel is the finite identity operator when summed against an input function and directly supplies pointwise Fourier reconstruction.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L75-L94

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

theorem NarrowDNF.Fourier.kernel {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x y : ι → Bool) :
    ProductMeasure.weight p y *
      (∑ s : ι → Bool, character p s x * character p s y) =
      if x = y then 1 else 0 := by sorry
