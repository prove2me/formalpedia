-- Prove2me | Theorems.Thm_NarrowDNF_Fourier_expansion
-- name    : NarrowDNF.Fourier.expansion
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:20:53.035912+00:00
-- url     : https://prove2.me/theorems/425fb15c-31ba-45fe-87b7-3f06de0ddf36
-- title:
--   Pointwise reconstruction by the biased Fourier expansion
-- statement:
--   Let \(I\) be finite, \(0<p<1\), and \(f:\{0,1\}^I\to\mathbb R\). For each \(S\subseteq I\), let
--   $$\chi_S^p(x)=\prod_{i\in S}\frac{x_i-p}{\sqrt{p(1-p)}},\qquad \widehat f_p(S)=\mathbb E_p[f(X)\chi_S^p(X)].$$
--   Then for every input \(x\),
--   $$f(x)=\sum_{S\subseteq I}\widehat f_p(S)\chi_S^p(x).$$
--   This is exact finite-dimensional reconstruction, with all subsets retained and no limiting or approximation argument. In particular, it holds for arbitrary real-valued input functions. The support subsets are equivalently the Boolean masks indexing the formal basis.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L97-L115

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
import Theorems.Thm_NarrowDNF_Fourier_kernel

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

theorem NarrowDNF.Fourier.expansion {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    (∑ s : ι → Bool, coefficient p f s * character p s x) = f x := by sorry
