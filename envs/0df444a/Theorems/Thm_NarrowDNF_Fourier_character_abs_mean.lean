-- Prove2me | Theorems.Thm_NarrowDNF_Fourier_character_abs_mean
-- name    : NarrowDNF.Fourier.character_abs_mean
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:11:51.101204+00:00
-- url     : https://prove2.me/theorems/21c467f0-fe10-4b08-aece-c0bc3f56da37
-- title:
--   The exact absolute first moment of a biased Fourier character
-- statement:
--   Let \(I\) be finite, \(0<p<1\), and \(S\subseteq I\). For \(X\) with independent Bernoulli-\(p\) coordinates, use the normalized character
--   $$\chi_S^p(x)=\prod_{i\in S}\frac{x_i-p}{\sqrt{p(1-p)}}.$$
--   Then
--   $$\mathbb E_p[|\chi_S^p(X)|]=(2\sqrt{p(1-p)})^{|S|}.$$
--   The support subset is represented by a Boolean mask in the formal statement, with degree \(|S|\). This computes the precise first absolute moment of the orthonormal basis function and supplies the factor needed for a safe Fourier coefficient bound at arbitrary bias.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L305-L320

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

theorem NarrowDNF.Fourier.character_abs_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (s : ι → Bool) :
    ProductMeasure.expectation p (fun x => |character p s x|) =
      (2 * Real.sqrt (p * (1-p))) ^ degree s := by sorry
