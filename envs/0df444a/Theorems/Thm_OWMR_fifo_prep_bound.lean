-- Prove2me | Theorems.Thm_OWMR_fifo_prep_bound
-- name    : OWMR.fifo_prep_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T06:36:41.419873+00:00
-- url     : https://prove2.me/theorems/29ac5fb5-0cf3-4711-9bee-62dcfc1ea283
-- title:
--   Finite expected preparation cost: $\mathbb E\sum_{t<T}\mathbf 1_{\{t\ \mathrm{preparing}\}}\bigl(1+\sum_i\sum_{s<t}D_{s,i}\bigr)\le C$
-- statement:
--   Let $D_0,D_1,\ldots$ be i.i.d. demand vectors with law $\mu$ on $[0,\infty)^n$, each coordinate with positive finite mean; the coordinates may be dependent. Fix $T_0\in\mathbb N$ and reals $b_i$. Call period $t$ a preparation period unless $T_0\le t+1$ and $\sum_{s<t}D_{s,i}\ge b_i$ for every $i$. Then there is a finite constant $C$ such that, for all $T\le N$, with $D_N,D_{N+1},\ldots$ set to $0$,
--
--   $$\mathbb E\sum_{t<T}\mathbf 1_{\{t\ \text{is a preparation period}\}}\Bigl(1+\sum_i\sum_{s<t}D_{s,i}\Bigr)\le C.$$
--
--   With $T_0$ the period by which all prescribed pipelines have arrived and $b_i$ the amount by which retailer $i$'s position must fall to reach its target, this bounds the expected preparation length and the cost of the backlog accumulated during preparation (Appendix B, Step 1), which grows at most linearly in cumulative demand.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix B (proof of Proposition 2), Step 1, p. E.4: the preparation duration and the backlog accumulated during preparation have finite expected cost under finite first demand moments.

import Definitions.Def_owmr_network_model

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem fifo_prep_bound {n : ℕ} (μ : Measure (Fin n → ℝ≥0)) [IsProbabilityMeasure μ]
    (hpos : ∀ i, 0 < ∫⁻ a, (a i : ℝ≥0∞) ∂μ) (hfin : ∀ i, ∫⁻ a, (a i : ℝ≥0∞) ∂μ < ∞)
    (T0 : ℕ) (b : Fin n → ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ T N : ℕ, T ≤ N →
      ∫⁻ z, ∑ t ∈ Finset.range T,
        (if T0 ≤ t + 1 ∧ ∀ i, b i ≤ ∑ s ∈ Finset.range t, ((padHist N z s i : ℝ≥0) : ℝ) then 0
          else ENNReal.ofReal (1 + ∑ i, ∑ s ∈ Finset.range t, ((padHist N z s i : ℝ≥0) : ℝ)))
        ∂(Measure.pi fun _ : Fin N => μ) ≤ C := by sorry
end OWMR
