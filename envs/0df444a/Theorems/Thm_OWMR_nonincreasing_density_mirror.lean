-- Prove2me | Theorems.Thm_OWMR_nonincreasing_density_mirror
-- name    : OWMR.nonincreasing_density_mirror
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T20:47:29.600201+00:00
-- url     : https://prove2.me/theorems/213eb394-c2b3-461e-a3cc-30bd9955f98f
-- title:
--   Lemma D.2 (nonincreasing-density mirror bound): if Y has a possible atom at 0 and a nonincreasing density on (0,w), then NV_{p,h}(Y) ≤ p(1-√(p/(p+h)))w
-- statement:
--   Let $(\Omega,\mathbb P)$ be a probability space and $Y$ a real random variable whose law is $c\,\delta_0+\varrho(x)\,dx$ on $(0,w)$: a possible mass $c\ge0$ at zero and a density $\varrho$ (with values in $[0,\infty]$) that is nonincreasing on $(0,w)$, with no mass elsewhere, where $w\ge0$. Then for $h,p>0$,
--   $$\mathrm{NV}_{p,h}(Y)=\inf_z\mathbb E[p(z-Y)^++h(Y-z)^+]\le p\Bigl(1-\sqrt{p/(p+h)}\Bigr)w.$$
--   No regularity of $\varrho$ beyond monotonicity is needed: it may jump and may be unbounded near zero.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix D, Lemma D.2 (Nonincreasing-Density Mirror Bound) with inequality (D.4) and the loss (D.1), p. E.24; proof in Appendix D.1, p. E.27.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Real.Sqrt

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem nonincreasing_density_mirror {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (h p w : ℝ) (hh : 0 < h)
    (hp : 0 < p) (hw : 0 ≤ w) (c : ℝ≥0∞) (ϱ : ℝ → ℝ≥0∞) (hϱ : AntitoneOn ϱ (Set.Ioo 0 w))
    (hlaw : P.map Y = c • Measure.dirac 0 + (volume.restrict (Set.Ioo 0 w)).withDensity ϱ) :
    ⨅ z : ℝ, ∫ ω, (p * max (z - Y ω) 0 + h * max (Y ω - z) 0) ∂P
      ≤ p * (1 - Real.sqrt (p / (p + h))) * w := by sorry
end OWMR
