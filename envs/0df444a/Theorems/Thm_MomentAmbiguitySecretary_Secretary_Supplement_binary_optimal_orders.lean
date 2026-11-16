-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_Supplement_binary_optimal_orders
-- name    : MomentAmbiguitySecretary.Secretary.Supplement.binary_optimal_orders
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:54:40.981297+00:00
-- url     : https://prove2.me/theorems/ccf7b4e2-9c3d-497c-9256-85d4e3501796
-- title:
--   Lemma 4.3 (used in the proof of Theorem 4.1) — Unique binary-law optimal orders and their exact optimal profits
-- statement:
--   Fix $\beta\in[1/2,1)$ and $\varepsilon\in(0,1)$, and any integers $B,n$ satisfying
--   $$B\ge\frac4{\varepsilon(1-\beta)},\qquad n>\max\{2B,2/(1-\beta)\}.$$
--   For the canonical binary laws, both optimum quantities are unique, and their actual optimal profits are
--   $$\operatorname*{argmax}_{q\ge0}\operatorname{Profit}_{\mu,\beta}(q)=\{B\},\quad \operatorname{Profit}_{\mu,\beta}^*=\beta B,$$
--   $$\operatorname*{argmax}_{q\ge0}\operatorname{Profit}_{\nu,\beta}(q)=\{1\},\quad \operatorname{Profit}_{\nu,\beta}^*=\beta.$$
--   The optima are suprema of the profit functions, not preset values. The parameter inequalities imply the binary construction's $n,B\ge3$.
--
--   Differences from the source: none.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Lemma 4.3, PDF/printed p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Newsvendor
import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Binary

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- Lemma 4.3, supplied preprint, PDF/printed p.10. -/
theorem binary_optimal_orders (β ε : ℝ) (hβ : β ∈ Ico (1 / 2) 1) (hε : ε ∈ Ioo 0 1)
    (n B : ℕ) (hB : 4 / (ε * (1 - β)) ≤ (B : ℝ))
    (hn : max (2 * (B : ℝ)) (2 / (1 - β)) < (n : ℝ)) :
    optimalOrders (binaryMu n B) β = {(B : ℝ)} ∧
    optimalProfit (binaryMu n B) β = β * (B : ℝ) ∧
    optimalOrders (binaryNu n B) β = {1} ∧
    optimalProfit (binaryNu n B) β = β := by sorry

end MomentAmbiguitySecretary.Secretary.Supplement
