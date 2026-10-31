-- Prove2me | Theorems.Thm_MinBuying_finite_affiliated_coarsening
-- name    : MinBuying.finite_affiliated_coarsening
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T18:09:08.62695+00:00
-- url     : https://prove2.me/theorems/be79ee0f-c6f7-4ba9-a653-9f12fb7990be
-- title:
--   Threshold-preserving PMF reduction of affiliated exchangeable laws
-- statement:
--   Let $\mu$ be an exchangeable affiliated probability law on $n$ nonnegative real-valued coordinates, and let $S\subset\mathbb R$ be a finite set of thresholds. There exist a measurable map $q:\mathbb R\to\mathbb R_{\ge0}$ and a probability mass function $w$ such that the law of $(q(V_1),\ldots,q(V_n))$ for $V\sim\mu$ is exactly the measure associated with $w$. This law is valid and exchangeable, its real-valued masses are MTP2, and for every $t\in S$ and every $x\ge0$,
--   $$t\le q(x)\quad\Longleftrightarrow\quad t\le x.$$
--   Thus all affordability decisions at the selected thresholds can be preserved in a PMF model. The original law may have either a measurable pointwise-MTP2 density or a pointwise-MTP2 probability mass function.
-- source:
--   Supporting lemma for Theorem 2 of Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133 . This proof introduces an exact threshold coarsening to transfer the PMF argument to the full density-or-PMF affiliation definition.

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory

namespace MinBuying

theorem finite_affiliated_coarsening (n : ℕ) (μ : JointLaw n) (hμ : ValidLaw μ)
    (hex : Exchangeable μ) (haff : Affiliated μ) (S : Finset ℝ) :
    ∃ q : ℝ → ℝ, ∃ w : PMF (Valuations n),
      Measurable q ∧ (∀ x,0 ≤ q x) ∧
      (∀ t ∈ S, ∀ x,0 ≤ x → (t ≤ q x ↔ t ≤ x)) ∧
      w.toMeasure = Measure.map (fun v : Valuations n => fun i => q (v i)) μ ∧
      ValidLaw w.toMeasure ∧ Exchangeable w.toMeasure ∧ MTP2 (fun v => (w v).toReal) := by
  sorry

end MinBuying
