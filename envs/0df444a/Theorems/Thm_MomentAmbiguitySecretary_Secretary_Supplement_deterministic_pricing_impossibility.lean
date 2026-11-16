-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_Supplement_deterministic_pricing_impossibility
-- name    : MomentAmbiguitySecretary.Secretary.Supplement.deterministic_pricing_impossibility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:56:01.8958+00:00
-- url     : https://prove2.me/theorems/deedd1f0-7963-4a1d-9a9e-ec3678cbecfe
-- title:
--   Theorem 5.1 (companion theorem; not used in the proof of the goal) — One fixed moment-equivalent pair defeats every positive deterministic price
-- statement:
--   For every $\varepsilon\in(0,1)$ there is one pair of nonnegative laws $\mu,\nu$, each having every finite natural moment and sharing the full moment sequence, such that their positive finite monopoly revenues satisfy, for every positive real price $v$,
--   $$\min\left\{\frac{\operatorname{Rev}_{\mu}(v)}{\operatorname{Rev}_{\mu}^*},\frac{\operatorname{Rev}_{\nu}(v)}{\operatorname{Rev}_{\nu}^*}\right\}<\varepsilon.$$
--   Here $\operatorname{Rev}_{\psi}(v)=v\Pr_\psi(X\ge v)$ and $\operatorname{Rev}_{\psi}^*=\sup_{v>0}\operatorname{Rev}_{\psi}(v)$. The pair is chosen before the price. Positivity of both denominators is explicit, as supplied by the source proof; finite first moments bound monopoly revenue.
--
--   Differences from the source:
--   - encoding: ratios to monopoly revenues of the constructed laws → positivity of each monopoly revenue is explicit alongside the ratios; reason: the source proof gives positive revenue lower bounds; all-moment laws give finite upper bounds, so division is well defined
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Theorem 5.1, PDF/printed p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Pricing

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- Theorem 5.1, supplied preprint, PDF/printed p.12. -/
theorem deterministic_pricing_impossibility (ε : ℝ) (hε : ε ∈ Ioo 0 1) :
    ∃ μ ν : Law, MomentEquivalent μ.val ν.val ∧
      0 < optimalRevenue (μ.val : Measure ℝ≥0) ∧
      0 < optimalRevenue (ν.val : Measure ℝ≥0) ∧
      ∀ v : ℝ, 0 < v →
        min (revenue (μ.val : Measure ℝ≥0) v / optimalRevenue (μ.val : Measure ℝ≥0))
          (revenue (ν.val : Measure ℝ≥0) v / optimalRevenue (ν.val : Measure ℝ≥0)) < ε := by sorry

end MomentAmbiguitySecretary.Secretary.Supplement
