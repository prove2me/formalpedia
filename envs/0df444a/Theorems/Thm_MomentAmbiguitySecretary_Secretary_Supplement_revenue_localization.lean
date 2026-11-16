-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_Supplement_revenue_localization
-- name    : MomentAmbiguitySecretary.Secretary.Supplement.revenue_localization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:56:28.441215+00:00
-- url     : https://prove2.me/theorems/beba64fc-62a0-40c3-aa14-4075c5382721
-- title:
--   Lemma 5.1 (used in the proof of Theorem 5.2) — Exact monopoly-revenue lower bound and off-interval revenue localization for every residue law
-- statement:
--   Fix integers $N,B\ge2$ and the published residue-family laws $\mu_h$, $0\le h<N$. Let $n_h$ be the unique integer in $[N-1,2N-2]$ congruent to $h$ modulo $N$, and $I_h=(B^{n_h-1},B^{n_h}]$. With the published exponent $e(j)$, the series
--   $$C_N=\sum_{j\notin[N-1,2N-2]}2^{2j-e(j)-(N-2)}$$
--   converges. For every residue $h$,
--   $$\operatorname{Rev}_{\mu_h}^*\ge B^{N-1}/4,\qquad
--   \operatorname{Rev}_{\mu_h}(v)\le(2^{2N-2}+C_N)B^{N-2}\quad(v>0,\ v\notin I_h).$$
--   The signed exponent, strict positivity of prices, and open-left/closed-right interval endpoints are retained. The summability conclusion records the convergence established in the source proof.
--
--   Differences from the source: none.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Lemma 5.1, PDF/printed p.13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Pricing

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- Lemma 5.1, supplied preprint, PDF/printed p.13. -/
theorem revenue_localization (N B : ℕ) (hN : 2 ≤ N) (hB : 2 ≤ B) :
    Summable (localizationTerm N) ∧
    ∀ h : Fin N,
      (B : ℝ) ^ (N - 1) / 4 ≤ optimalRevenue (residueMeasure B N h.val) ∧
      ∀ v : ℝ, 0 < v → v ∉ localizationInterval B N h.val →
        revenue (residueMeasure B N h.val) v ≤
          ((2 : ℝ) ^ (2 * N - 2) + localizationC N) * (B : ℝ) ^ (N - 2) := by sorry

end MomentAmbiguitySecretary.Secretary.Supplement
