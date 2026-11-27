-- Prove2me | Theorems.Thm_MPBSelect_Supplement_theorem_2
-- name    : MPBSelect.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:48:21.131159+00:00
-- url     : https://prove2.me/theorems/4d53d36d-3d30-4131-ab01-742b5af1087f
-- title:
--   Theorem 2 — balance-weighted lower bound for the exact false-selection rate
-- statement:
--   Let $W_i(\theta_b)$ be the exact balance weight (17): on $\Xi$, it is
--   $\max\{\min(\min_{j\ne i^*}d_j,d_i/2)/p_b,1\}$ when $\theta_b\in\Theta_{i^*}$ and $\max\{d_i/p_b,1\}$ otherwise; off $\Xi$ it is $+\infty$.
--
--   **Theorem 2.** For every feasible fixed allocation $\boldsymbol\alpha$,
--
--   $$
--   \min_{j\ne i^*}\widetilde{\mathrm{LDR}}_{j,i^*}
--   \ge \min_{(i,\theta_b)\in\Xi}W_i(\theta_b)\widetilde G_i(\theta_b).
--   $$
--
--   This is the first relaxation of the exact OCBA objective.
--
--   Differences from the source:
--   - encoding: $W_i(\theta_b)=+\infty$ off $\Xi$ → the real-valued weight is evaluated only on the nonempty finite set $\Xi$; reason: the minimum has exactly the same terms and no artificial real value represents infinity
--   - encoding: “given fixed $\alpha$” under the static-allocation section → $\alpha$ is explicitly required to lie in the allocation simplex; reason: this is the standing meaning of a fixed allocation on p.11
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, Theorem 2, (17), p.15

import Mathlib
import Definitions.Def_MPBSelect_feasibleSet
import Definitions.Def_MPBSelect_Supplement_ExactRates

namespace MPBSelect.Supplement

/-- **Theorem 2 (balance-weight relaxation).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, Theorem 2,
p.15, equation (17).

For every fixed feasible allocation, the exact false-selection rate is at least the minimum of
`W_i(θ_b) G̃_i(θ_b)` over `Ξ`, with the exact two branches and constants of (17). -/
theorem theorem_2 {k B : ℕ} (P : MPBSelect.Problem k B)
    (α : Fin k → Fin B → ℝ) (hα : α ∈ MPBSelect.feasibleSet k B) :
    weightedExactRate P α ≤ exactFSRate P α := by sorry

end MPBSelect.Supplement
