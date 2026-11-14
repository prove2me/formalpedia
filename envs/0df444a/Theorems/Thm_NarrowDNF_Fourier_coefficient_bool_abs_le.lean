-- Prove2me | Theorems.Thm_NarrowDNF_Fourier_coefficient_bool_abs_le
-- name    : NarrowDNF.Fourier.coefficient_bool_abs_le
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:19:45.325364+00:00
-- url     : https://prove2.me/theorems/a1467e0b-d341-4cf3-844e-b75fe1cf6f31
-- title:
--   A uniform absolute Fourier coefficient bound for Boolean functions
-- statement:
--   Let \(I\) be finite, \(0<p<1\), and \(f:\{0,1\}^I\to\{0,1\}\). Regard the Boolean values as the real numbers zero and one. For \(S\subseteq I\), define
--   $$\chi_S^p(x)=\prod_{i\in S}\frac{x_i-p}{\sqrt{p(1-p)}},\qquad \widehat f_p(S)=\mathbb E_p[f(X)\chi_S^p(X)].$$
--   Then
--   $$|\widehat f_p(S)|\le(2\sqrt{p(1-p)})^{|S|}.$$
--   The bound holds for every Boolean function, without a monotonicity assumption. It controls each coefficient by the exact absolute first moment of its character and retains the degree-dependent factor two.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L322-L339

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
import Theorems.Thm_NarrowDNF_Fourier_character_abs_mean

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

theorem NarrowDNF.Fourier.coefficient_bool_abs_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (s : ι → Bool) :
    |coefficient p (fun x => Influence.boolValue (f x)) s| ≤
      (2 * Real.sqrt (p * (1-p))) ^ degree s := by sorry
