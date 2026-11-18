-- Prove2me | Theorems.Thm_OWMR_arb_indep_max
-- name    : OWMR.arb_indep_max
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T12:51:30.810719+00:00
-- url     : https://prove2.me/theorems/808b22e5-011a-448c-89c4-27cb2e4579f9
-- title:
--   Lemma C.2: a trigger level for the largest of $L$ i.i.d. demands
-- statement:
--   Let $\rho$ be a law on $[0,\infty)$ with finite mean, $L\in\mathbb N$ and $h,p>0$, let $V_1,\ldots,V_L$ be i.i.d. with law $\rho$, and $\phi(y)=hy^++py^-$. Then there is $y\ge0$ with
--   $$(h+p)\Bigl(\frac{h}{h+p}\,y+\mathbb E\bigl(\max_jV_j-y\bigr)^+\Bigr)\le\Bigl(1+\frac hp\Bigr)\inf_z\mathbb E\,\phi\Bigl(z-\sum_jV_j\Bigr)+h\,\mathbb E V_1 .$$
--   Here $y$ is the trigger level; the left side bounds the expected reserve cost charged to a period in which the supplier runs short.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix C, Step 1, Lemma C.2 with (C.2)-(C.6), pp. E.8-E.10.

import Definitions.Def_owmr_consolidation_policy

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem arb_indep_max (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : ∫⁻ x, (x : ℝ≥0∞) ∂ρ < ∞)
    (L : ℕ) (h p : ℝ) (hh : 0 < h) (hp : 0 < p) :
    ∃ y : ℝ, 0 ≤ y ∧
      (h + p) * (h / (h + p) * y
          + ∫ w, max (((Finset.univ.sup w : ℝ≥0) : ℝ) - y) 0 ∂(Measure.pi fun _ : Fin L => ρ))
        ≤ (1 + h / p) * (⨅ z : ℝ, ∫ w, whLoss h p (z - ∑ j, (w j : ℝ))
            ∂(Measure.pi fun _ : Fin L => ρ))
          + h * ∫ x, (x : ℝ) ∂ρ := by sorry
end OWMR
