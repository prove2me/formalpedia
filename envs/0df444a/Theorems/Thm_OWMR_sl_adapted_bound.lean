-- Prove2me | Theorems.Thm_OWMR_sl_adapted_bound
-- name    : OWMR.sl_adapted_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T04:27:02.019864+00:00
-- url     : https://prove2.me/theorems/c554cf92-c5d4-4542-99ff-c55111dfd217
-- title:
--   Finite-horizon single-location bound for adapted positions: $TJ\le\mathbb E\sum_{t<T}[K\mathbf 1_{\{q_t>0\}}+f(x_t)]+K$
-- statement:
--   Let $d_0,d_1,\ldots$ be i.i.d. with law $\mu$ on a measurable space $\alpha$, independent of auxiliary randomness $u\sim\nu$, and let $g:\alpha\to[0,\infty)$ be measurable, so that the demand of period $s$ is $g(d_s)$. Let the orders $q_t(u,d)\ge0$ be measurable and depend on $d$ only through $d_0,\ldots,d_{t-1}$, and let
--
--   $$x_t=y_0+\sum_{s\le t}q_s-\sum_{s<t}g(d_s)$$
--
--   be the position after the order of period $t$. Let $f\ge0$ be measurable, and let $(J,v)$ be a bounded subsolution: $v$ is measurable, $-K\le v\le0$, and
--
--   $$J\le f(y)+\mathbb E\,v\bigl(y-g(d)\bigr)-v(y)\qquad(y\in\mathbb R).$$
--
--   Then for all horizons $T\le N$, with $d_N,d_{N+1},\ldots$ set to $0$ (periods before $T$ never use them),
--
--   $$\max(TJ,0)\le\mathbb E\sum_{t<T}\bigl[K\mathbf 1_{\{q_t>0\}}+f(x_t)\bigr]+K .$$
--
--   This is the finite-horizon bound (6) of Lemma 1 for policies that also use network history and auxiliary randomness, as Proposition 3 requires.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Lemma 1, Section 4.1, p. 11 (equations (5) and (6)), and Appendix A (proof of Lemma 1); used in Steps 2 and 3 of the proof of Proposition 3, Section 5.3, pp. 24-25.

import Definitions.Def_owmr_network_model

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem sl_adapted_bound {α U : Type} [MeasurableSpace α] [Zero α] [MeasurableSpace U]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure U) [IsProbabilityMeasure ν]
    (g : α → ℝ≥0) (hg : Measurable g) (q : ℕ → U → (ℕ → α) → ℝ)
    (hna : ∀ (t : ℕ) (u : U) (d d' : ℕ → α), (∀ s < t, d s = d' s) → q t u d = q t u d')
    (hqm : ∀ t, Measurable fun ω : U × (ℕ → α) => q t ω.1 ω.2)
    (hq0 : ∀ t u d, 0 ≤ q t u d) (y0 : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ y, 0 ≤ f y) (K J : ℝ) (v : ℝ → ℝ) (hv : Measurable v)
    (hvb : ∀ y, -K ≤ v y ∧ v y ≤ 0)
    (hsub : ∀ y, J ≤ f y + ∫ a, v (y - (g a : ℝ)) ∂μ - v y) (T N : ℕ) (hTN : T ≤ N) :
    ENNReal.ofReal (T * J)
      ≤ ∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal
          (K * (if 0 < q t ω.1 (padHist N ω.2) then 1 else 0)
            + f (y0 + ∑ s ∈ Finset.range (t + 1), q s ω.1 (padHist N ω.2)
              - ∑ s ∈ Finset.range t, (g (padHist N ω.2 s) : ℝ)))
          ∂(ν.prod (Measure.pi fun _ : Fin N => μ)) + ENNReal.ofReal K := by sorry
end OWMR
