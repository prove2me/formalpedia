-- Prove2me | Theorems.Thm_NarrowDNF_Fourier_variance_le_spectralEnergy
-- name    : NarrowDNF.Fourier.variance_le_spectralEnergy
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:26:30.98348+00:00
-- url     : https://prove2.me/theorems/7706725f-ddda-467a-83f1-44976eb92479
-- title:
--   Variance is bounded by degree-weighted Fourier energy
-- statement:
--   Let \(I\) be finite, \(0<p<1\), and \(f:\{0,1\}^I\to\mathbb R\). With \(\chi_S^p(x)=\prod_{i\in S}\frac{x_i-p}{\sqrt{p(1-p)}}\) and \(\widehat f_p(S)=\mathbb E_p[f\chi_S^p]\),
--   $$\operatorname{Var}_p(f)\le\sum_{S\subseteq I}|S|\,\widehat f_p(S)^2.$$
--   Here variance means \(\mathbb E_p[(f-\mathbb E_p f)^2]\). This spectral Poincaré estimate bounds fluctuations by degree-weighted energy; the empty-support coefficient contributes zero on the right.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/Fourier.lean#L370-L387

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
import Theorems.Thm_NarrowDNF_Fourier_inner_parseval
import Theorems.Thm_NarrowDNF_Influence_variance_eq_secondMoment

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

theorem NarrowDNF.Fourier.variance_le_spectralEnergy {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) :
    Influence.variance p f ≤ ∑ s : ι → Bool, (degree s : ℝ) * coefficient p f s ^ 2 := by sorry
