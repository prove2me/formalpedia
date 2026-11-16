-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_Supplement_newsvendor_impossibility
-- name    : MomentAmbiguitySecretary.Secretary.Supplement.newsvendor_impossibility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:55:19.844413+00:00
-- url     : https://prove2.me/theorems/1cbddfee-3975-45bd-a259-a32d25f7cd13
-- title:
--   Theorem 4.1 (companion theorem; not used in the proof of the goal) — The specified binary pair defeats every finite-mean randomized order with strict ratio below epsilon
-- statement:
--   Fix $\beta\in[1/2,1)$ and $\varepsilon\in(0,1)$, and any integers $B,n$ satisfying
--   $$B\ge4/(\varepsilon(1-\beta)),\qquad n>\max\{2B,2/(1-\beta)\}.$$
--   The canonical binary pair defeats every finite-first-moment randomized order law $\lambda$:
--   $$\min\left\{\frac{\operatorname{Profit}_{\mu,\beta}(\lambda)}{\operatorname{Profit}_{\mu,\beta}^*},\frac{\operatorname{Profit}_{\nu,\beta}(\lambda)}{\operatorname{Profit}_{\nu,\beta}^*}\right\}<\varepsilon.$$
--   The laws are fixed before the order lottery, and net profits retain negative values. The denominators are actual optimal profits, positive by Lemma 4.3.
--
--   Differences from the source: none.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Theorem 4.1, PDF/printed p.11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Newsvendor
import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Binary

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- Theorem 4.1, supplied preprint, PDF/printed p.11. -/
theorem newsvendor_impossibility (β ε : ℝ) (hβ : β ∈ Ico (1 / 2) 1) (hε : ε ∈ Ioo 0 1)
    (n B : ℕ) (hB : 4 / (ε * (1 - β)) ≤ (B : ℝ))
    (hn : max (2 * (B : ℝ)) (2 / (1 - β)) < (n : ℝ)) :
    ∀ lottery : OrderLaw,
      min (randomizedProfit (binaryMu n B) β lottery / optimalProfit (binaryMu n B) β)
        (randomizedProfit (binaryNu n B) β lottery / optimalProfit (binaryNu n B) β) < ε := by sorry

end MomentAmbiguitySecretary.Secretary.Supplement
