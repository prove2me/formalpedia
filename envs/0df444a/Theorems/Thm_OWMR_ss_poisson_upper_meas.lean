-- Prove2me | Theorems.Thm_OWMR_ss_poisson_upper_meas
-- name    : OWMR.ss_poisson_upper_meas
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T12:51:30.746435+00:00
-- url     : https://prove2.me/theorems/79178106-bfed-47bd-b12e-c5b653b5d79c
-- title:
--   Finite-horizon $(s,S)$ upper bound from a random start, for measurable locally bounded costs
-- statement:
--   Let $\alpha$ be a measurable space with a point $0$, let $d_0,d_1,\ldots$ be i.i.d. with law $\mu$ on $\alpha$, and let $g:\alpha\to[0,\infty)$ be measurable, so that the demands $g(d_t)$ have law $\rho$ with $0<\mathbb E\,g(d)$. Let $f:\mathbb R\to[0,\infty)$ be measurable and bounded above on every bounded interval, and let $K\ge0$, $s\le S$ and $M$ be reals. Let $\mathrm{act}_t$ (an event) and $X_t$ (a real number) be measurable functions of the path that depend only on $d_0,\ldots,d_{t-1}$. Suppose that once active the process stays active and follows the $(s,S)$ rule $X_{t+1}=\widehat X_t-g(d_t)$, with $\widehat X_t=S$ if $X_t\le s$ and $\widehat X_t=X_t$ otherwise, and that it starts at most $M$. Then there is a finite $C$ such that, for all $T\le N$, with $d_N,d_{N+1},\ldots$ set to $0$,
--   $$\mathbb E\sum_{t<T}\mathbf 1_{\mathrm{act}_t}\bigl[K\mathbf 1_{\{X_t\le s,\ X_t<S\}}+f(\widehat X_t)\bigr]\le T\,c_\rho(f;K,s,S)+C,$$
--   where $c_\rho(f;K,s,S)$ (`ssAvgCost`) is the long-run average cost of the $(s,S)$ policy started at $S$.
--
--   This extends the bound for continuous $f$ to the costs used in Appendix C: the stockout probability $\mathbb P(D^{(L_0)}>y)$ and the width loss $\psi((S-y)/w)$.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix B (proof of Proposition 2), Step 4, p. E.4, and its use in Appendix C, Steps 4 and 8, pp. E.14-E.16 and E.21-E.22; renewal-reward identities (10) and (11), pp. 13-14.

import Definitions.Def_owmr_single_location

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem ss_poisson_upper_meas {α : Type} [MeasurableSpace α] [Zero α]
    (μ : Measure α) [IsProbabilityMeasure μ] (g : α → ℝ≥0) (hg : Measurable g)
    (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρg : μ.map g = ρ)
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (f : ℝ → ℝ) (hfm : Measurable f)
    (hfb : ∀ a b : ℝ, ∃ C, ∀ y ∈ Set.Icc a b, f y ≤ C) (hf0 : ∀ y, 0 ≤ f y)
    (K s S M : ℝ) (hK : 0 ≤ K) (hsS : s ≤ S)
    (act : ℕ → (ℕ → α) → Prop) [∀ t, DecidablePred (act t)] (X : ℕ → (ℕ → α) → ℝ)
    (hactm : ∀ t, MeasurableSet {d | act t d}) (hXm : ∀ t, Measurable (X t))
    (hactd : ∀ (t : ℕ) (d d' : ℕ → α), (∀ r < t, d r = d' r) → (act t d ↔ act t d'))
    (hXd : ∀ (t : ℕ) (d d' : ℕ → α), (∀ r < t, d r = d' r) → X t d = X t d')
    (hmono : ∀ t d, act t d → act (t + 1) d)
    (hstep : ∀ t d, act t d → X (t + 1) d = (if X t d ≤ s then S else X t d) - (g (d t) : ℝ))
    (hstart0 : ∀ d, act 0 d → X 0 d ≤ M)
    (hstart : ∀ t d, ¬ act t d → act (t + 1) d → X (t + 1) d ≤ M) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ T N : ℕ, T ≤ N →
      ∫⁻ z, ∑ t ∈ Finset.range T, (if act t (padHist N z) then ENNReal.ofReal
          (K * (if X t (padHist N z) ≤ s ∧ X t (padHist N z) < S then 1 else 0)
            + f (if X t (padHist N z) ≤ s then S else X t (padHist N z))) else 0)
        ∂(Measure.pi fun _ : Fin N => μ)
      ≤ T * ssAvgCost ρ f K s S + C := by sorry
end OWMR
