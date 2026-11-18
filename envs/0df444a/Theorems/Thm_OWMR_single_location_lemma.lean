-- Prove2me | Theorems.Thm_OWMR_single_location_lemma
-- name    : OWMR.single_location_lemma
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T19:10:56.893629+00:00
-- url     : https://prove2.me/theorems/cd877e0f-1ee5-42c2-956c-16c8b45ce419
-- title:
--   Lemma 1 (Single-Location Inventory Problem): canonical $(\hat s,\hat S)$ optimality, a cost transfer $u$ with $\operatorname{osc}(u)\le K$, and the bound $TJ-K$
-- statement:
--   Let the one-period demand $D\ge0$ have law $\rho$ on $[0,\infty)$ with $0<\mathbb E D<\infty$, let $f:\mathbb R\to[0,\infty)$ be convex, coercive ($f(x)\to\infty$ as $|x|\to\infty$) and globally Lipschitz, and fix a setup cost $K\ge0$. In the single-location inventory problem with cost $f$, in each period $t$ the position may be raised by $q_t\ge0$ at cost $K\mathbf 1_{\{q_t>0\}}$, the post-action position $x_t$ incurs $f(x_t)$, and an i.i.d. demand $D_t$ then reduces it. Its value $J=J_D(f;K)$ (`slValue`) is the infimum, over all nonanticipative policies that may randomize independently of demand, of the long-run average cost
--   $$\limsup_{T\to\infty}\frac1T\,\mathbb E\sum_{t=0}^{T-1}\bigl[K\mathbf 1_{\{q_t>0\}}+f(x_t)\bigr]$$
--   from initial position $0$. Then $J$ is a finite number with $J\ge0$, and:
--
--   1. **Initial position.** The same infimum from any initial position $y_0\in\mathbb R$ equals $J$.
--   2. **Optimal $(s,S)$ rules.** If $s\le S$ and the $(s,S)$ policy started at $S$ has long-run average cost $J$, then from every initial position the rule that orders up to $S$ whenever the pre-action position is at most $s$, and does not order otherwise, has long-run average cost $J$.
--   3. **Positive setup cost.** If $K>0$, there are $\hat s<\hat S$ such that the $(\hat s,\hat S)$ policy started at $\hat S$ has long-run average cost $J$ and the canonical conditions hold:
--   $$f(\hat s)=J,\qquad f(\hat S)\le J,\qquad f(x)\le J\quad(\hat s\le x\le\hat S).$$
--   Its post-action positions lie in $(\hat s,\hat S]$, and its cycle length $\tau=\min\{t\ge1:\ \text{the pre-action position in period }t\text{ is at most }\hat s\}$ has $\mathbb E\,\tau^m<\infty$ for every $m\in\mathbb N$.
--   4. **Zero setup cost.** If $K=0$, there is a minimizer $x^*$ of $f$ with $J=f(x^*)=\min f$, and base stock at $x^*$ has long-run average cost $J$.
--   5. **Cost transfers.** There is a measurable function $u$ with oscillation $\sup u-\inf u\le K$, and $u=0$ if $K=0$, such that
--   $$J+(f(x)-J)^+\le f(x)+\mathbb E\bigl[u(x-D)-u(x)\bigr]\qquad(x\in\mathbb R).$$
--   6. **Finite horizons.** Let $\xi_0,\xi_1,\ldots$ be i.i.d. random elements (for example, demand vectors of a network), independent of auxiliary randomness $V$, with $D_t=g(\xi_t)$ distributed as $\rho$. For every policy whose order $q_t\ge0$ is a measurable function of $V$ and $\xi_0,\ldots,\xi_{t-1}$, and every initial position $y_0$, the post-action positions $x_t=y_0+\sum_{r\le t}q_r-\sum_{r<t}D_r$ satisfy
--   $$TJ-K\le\mathbb E\sum_{t=0}^{T-1}\bigl[K\mathbf 1_{\{q_t>0\}}+f(x_t)\bigr]\qquad(T\ge1).$$
--
--   This is Lemma 1 of the source. It combines the classical average-cost optimality of $(s,S)$ policies (Iglehart 1963; Zheng 1991; Feinberg and Lewis 2018), here for real positions and every demand law with finite positive mean, with the bounded cost-transfer function and the finite-horizon bound used for the shared-cost lower bound (Proposition 3), where the history may include network demand and auxiliary randomness.
--
--   **Formalization note.** In item 2 the rule is stated recursively on the history: the order in period $t$ is $S-y_t$ if the pre-action position $y_t=x_t-q_t$ is at most $s$, and $0$ otherwise; the long-run average cost is that of the deterministic policy. In item 3 the moments are taken under the product law of $(D_0,D_1,\ldots)$ (`Measure.infinitePi`). In item 6 the left side is read as $\max(TJ-K,0)$, the right side being nonnegative, and the expectation is over $V$ and $\xi_0,\ldots,\xi_{T-1}$.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 4.1 (Single-Location Inventory Problems), Lemma 1 (Single-Location Inventory Problem) with equations (4), (5) and (6), p. 12, and the paragraph before it (value independent of the initial position); proved in Appendix A, pp. E.1-E.3.

import Definitions.Def_owmr_single_location
import Mathlib.Probability.ProductMeasure

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem single_location_lemma (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ0 : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (hρ1 : ∫⁻ x, (x : ℝ≥0∞) ∂ρ < ∞)
    (f : ℝ → ℝ) (hf0 : ∀ y, 0 ≤ f y) (hfcv : ConvexOn ℝ Set.univ f)
    (hfco : ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ f y) (hfL : ∃ L : ℝ≥0, LipschitzWith L f)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ J : ℝ, 0 ≤ J ∧ slValue ρ f K = ENNReal.ofReal J ∧
      (∀ y0 : ℝ, (⨅ (U : Type) (_ : MeasurableSpace U) (ν : Measure U)
          (_ : IsProbabilityMeasure ν) (q : SLPolicy U) (_ : SLAdmissible q),
            slAvgCost ρ f K y0 q ν) = slValue ρ f K) ∧
      (∀ s S : ℝ, s ≤ S → ssAvgCost ρ f K s S = slValue ρ f K → ∀ y0 : ℝ,
        ∃ q : SLPolicy Unit, SLAdmissible q ∧
          (∀ (t : ℕ) (d : ℕ → ℝ≥0), q t () d = if slPos y0 q () d t - q t () d ≤ s
            then S - (slPos y0 q () d t - q t () d) else 0) ∧
          slAvgCost ρ f K y0 q (Measure.dirac ()) = slValue ρ f K) ∧
      (0 < K → ∃ s S : ℝ, IsCanonicalOptimum ρ f K s S ∧
        (∀ (d : ℕ → ℝ≥0) (t : ℕ), s < ssPost s S d t ∧ ssPost s S d t ≤ S) ∧
        ∀ m : ℕ, ∫⁻ d, (⨅ (t : ℕ) (_ : 1 ≤ t ∧ ssPre s S d t ≤ s), (t : ℝ≥0∞)) ^ m
          ∂(Measure.infinitePi fun _ : ℕ => ρ) < ∞) ∧
      (K = 0 → ∃ x : ℝ, (∀ y, f x ≤ f y) ∧ J = f x ∧ ssAvgCost ρ f K x x = slValue ρ f K) ∧
      (∃ u : ℝ → ℝ, Measurable u ∧ (∀ y z, u y - u z ≤ K) ∧ (K = 0 → ∀ y, u y = 0) ∧
        ∀ y, J + max (f y - J) 0 ≤ f y + ∫ d, u (y - (d : ℝ)) ∂ρ - u y) ∧
      (∀ {α U : Type} [MeasurableSpace α] [Zero α] [MeasurableSpace U]
        (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure U) [IsProbabilityMeasure ν]
        (g : α → ℝ≥0), Measurable g → μ.map g = ρ →
        ∀ q : ℕ → U → (ℕ → α) → ℝ,
          (∀ (t : ℕ) (u : U) (d d' : ℕ → α), (∀ r < t, d r = d' r) → q t u d = q t u d') →
          (∀ t, Measurable fun ω : U × (ℕ → α) => q t ω.1 ω.2) → (∀ t u d, 0 ≤ q t u d) →
          ∀ (y0 : ℝ) (T : ℕ), 1 ≤ T →
            ENNReal.ofReal (T * J - K) ≤ ∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal
              (K * (if 0 < q t ω.1 (padHist T ω.2) then 1 else 0)
                + f (y0 + ∑ s ∈ Finset.range (t + 1), q s ω.1 (padHist T ω.2)
                  - ∑ s ∈ Finset.range t, (g (padHist T ω.2 s) : ℝ)))
              ∂(ν.prod (Measure.pi fun _ : Fin T => μ))) := by sorry
end OWMR
