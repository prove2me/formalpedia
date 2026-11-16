-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_Supplement_randomized_pricing_impossibility
-- name    : MomentAmbiguitySecretary.Secretary.Supplement.randomized_pricing_impossibility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:57:05.748575+00:00
-- url     : https://prove2.me/theorems/f236ba4c-40e6-4454-9746-337cac5950cf
-- title:
--   Theorem 5.2 (companion theorem; not used in the proof of the goal) — One finite family sharing every moment defeats every randomized positive-price law
-- statement:
--   For every $\varepsilon>0$ there exist an integer $N\ge2$ and nonnegative laws $\mu_0,\ldots,\mu_{N-1}$, all with every finite moment and identical moment sequences, such that every Borel probability price law $\lambda$ on $(0,\infty)$ has an index $h<N$ satisfying
--   $$\frac{\operatorname{Rev}_{\mu_h}(\lambda)}{\operatorname{Rev}_{\mu_h}^*}<\varepsilon.$$
--   Each monopoly revenue is positive and finite. The entire family is fixed before the lottery; only $h$ may depend on it. No finite mean or support restriction is imposed on $\lambda$: its revenue integrand is bounded by the buyer's finite mean.
--
--   Differences from the source:
--   - encoding: ratios to monopoly revenues of the constructed laws → positivity of each monopoly revenue is explicit alongside the ratios; reason: the source proof gives positive revenue lower bounds; all-moment laws give finite upper bounds, so division is well defined
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Theorem 5.2, PDF/printed p.13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Pricing

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- Theorem 5.2, supplied preprint, PDF/printed p.13. -/
theorem randomized_pricing_impossibility (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ laws : Fin N → Law,
      (∀ h k : Fin N, MomentEquivalent (laws h).val (laws k).val) ∧
      (∀ h : Fin N, 0 < optimalRevenue ((laws h).val : Measure ℝ≥0)) ∧
      ∀ lottery : PriceLaw, ∃ h : Fin N,
        randomizedRevenue ((laws h).val : Measure ℝ≥0) lottery /
          optimalRevenue ((laws h).val : Measure ℝ≥0) < ε := by sorry

end MomentAmbiguitySecretary.Secretary.Supplement
