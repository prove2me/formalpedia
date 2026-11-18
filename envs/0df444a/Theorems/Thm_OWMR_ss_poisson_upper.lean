-- Prove2me | Theorems.Thm_OWMR_ss_poisson_upper
-- name    : OWMR.ss_poisson_upper
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T06:36:41.797403+00:00
-- url     : https://prove2.me/theorems/a5a973a1-a3f7-4f98-ab09-91e9ffeb742b
-- title:
--   Finite-horizon upper bound for an $(s,S)$ process started at a random time: $\mathbb E\sum_{t<T}\mathbf 1_{\mathrm{act}_t}[K\mathbf 1_{\{\mathrm{order}\}}+f(\widehat X_t)]\le T\,c(s,S)+C$
-- statement:
--   Let $\alpha$ be a measurable space with a point $0$, let $d_0,d_1,\ldots$ be i.i.d. with law $\mu$ on $\alpha$, and let $g:\alpha\to[0,\infty)$ be measurable, so that the demands $g(d_t)$ have law $\rho$ with $0<\mathbb E\,g(d)$. Let $f:\mathbb R\to[0,\infty)$ be continuous, and let $K\ge0$, $s\le S$ and $M$ be reals. Let $\mathrm{act}_t$ (an event) and $X_t$ (a real number) be measurable functions of the path that depend only on $d_0,\ldots,d_{t-1}$. Suppose that once active the process stays active and follows the $(s,S)$ rule,
--
--   $$X_{t+1}=\widehat X_t-g(d_t),\qquad \widehat X_t=S\ \text{if}\ X_t\le s,\quad \widehat X_t=X_t\ \text{otherwise},$$
--
--   and that it starts at most $M$: $X_0\le M$ if $\mathrm{act}_0$, and $X_{t+1}\le M$ whenever $\mathrm{act}_{t+1}$ holds but $\mathrm{act}_t$ does not. Then there is a finite constant $C$ such that, for all $T\le N$, with $d_N,d_{N+1},\ldots$ set to $0$,
--
--   $$\mathbb E\sum_{t<T}\mathbf 1_{\mathrm{act}_t}\bigl[K\mathbf 1_{\{X_t\le s,\ X_t<S\}}+f(\widehat X_t)\bigr]\le T\,c_\rho(f;K,s,S)+C,$$
--
--   where $c_\rho(f;K,s,S)$ (`ssAvgCost`) is the long-run average cost of the $(s,S)$ policy started at $S$, with setup cost $K$ per positive order and cost $f$ of the post-order position.
--
--   This is the bound used in Appendix B, Step 4, in a form that applies from a random start time. It is applied to the supplier policy on the aggregate position, to each retailer's $(s_i,S_i)$ policy, and to the mirror losses ($K=0$).
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix B (proof of Proposition 2, from p. E.4), Step 4: the bounds $\mathcal C_\ell(m)\le m\bar c_\ell+e_\ell(T)$ for the supplier policy and the retailer policies started after preparation, with the renewal-reward identities (10) and (11) of Section 4.2, pp. 13-14.

import Definitions.Def_owmr_single_location

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem ss_poisson_upper {α : Type} [MeasurableSpace α] [Zero α]
    (μ : Measure α) [IsProbabilityMeasure μ] (g : α → ℝ≥0) (hg : Measurable g)
    (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρg : μ.map g = ρ)
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y)
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
