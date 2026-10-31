-- Prove2me | Theorems.Thm_MarketplaceScalability_quasiconcave_pi
-- name    : MarketplaceScalability.quasiconcave_pi
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:49.583572+00:00
-- url     : https://prove2.me/theorems/0af610ae-54e7-474e-9670-5baa987c75cd
-- title:
--   Proof of Lemma 2 — $\pi$ is quasi-concave (corrected: demand conditions)
-- statement:
--   $\pi$ is quasi-concave on $(0,\bar c]$, and strictly so: for $p_1<p_2<p_3$ in $(0,\bar c]$,
--   $$
--   \min\{\pi(p_1),\pi(p_3)\}<\pi(p_2).
--   $$
--
--   The strict form gives the uniqueness of the optimal price.
--
--   Differences from the source:
--   - correction: D > 0, D′ < 0, D″ ≤ 0, D(0) = ∞ on outputs q ≥ 0 (p.4) → outputs in J = (0, q̄), the signs on J, and (1 − α)D(q) = p solvable in J for every p ∈ (0, c̄]; reason: the printed conditions are unsatisfiable: a positive concave function on (0, ∞) cannot be strictly decreasing, and a concave function on (0, b) cannot tend to +∞ at 0; solvability of the first-order condition is the only use of D(0) = ∞
--   - generalization: α a commission rate, Assumption 2 → 0 ≤ α < 1, and of Assumption 2 only f < F; reason: the argument uses no more, and low-type sellers are absent at μ = 1; every source instance, with α ∈ (0, 1), is covered
--   - encoding: c ∈ (c̲, c̄) with no sign on c̲ (p.6) → 0 < c̲; reason: (1 − α)D(q(c̲)) = c̲ with D > 0 and α < 1 forces c̲ > 0, so no source instance is excluded
--   - encoding: quasi-concave in p → on (0, c̄]; reason: under the corrected conditions the first-order condition is guaranteed solvable only on (0, c̄], and the proof of Proposition 1 uses no other prices
--   - generalization: quasi-concave → also the strict form; reason: the printed argument gives it (π′ has no flat stretch), it is an extra conclusion, and Mathlib has no strict notion here
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, proof of Lemma 2, p.25

import Mathlib
import Definitions.Def_MarketplaceScalability_Model
import Definitions.Def_MarketplaceScalability_Params_pi

namespace MarketplaceScalability

/-- **Quasi-concavity, proof of Lemma 2, p.25.** Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484: "We claim first that π(p) is quasi-concave in
p when D″(q) ≤ 0." and "which means π(p) is quasi-concave in p."

`π` is quasi-concave on `(0, c̄]`, and strictly so: between two prices it is strictly above the
smaller of the two endpoint values.

**Formalization Note** The strict form is what the printed derivative argument gives: `π′` changes sign at
most once, with no flat stretch. It is written out because Mathlib has no strict quasi-concavity at
this revision. The source's "the price that maximizes π(p)" (p.8) needs it. -/
theorem quasiconcave_pi (M : Model) :
    QuasiconcaveOn ℝ (Set.Ioc 0 M.cbar) M.pi ∧
    ∀ p₁ ∈ Set.Ioc 0 M.cbar, ∀ p₂ ∈ Set.Ioc 0 M.cbar, ∀ p₃ ∈ Set.Ioc 0 M.cbar,
      p₁ < p₂ → p₂ < p₃ → min (M.pi p₁) (M.pi p₃) < M.pi p₂ := by sorry

end MarketplaceScalability
