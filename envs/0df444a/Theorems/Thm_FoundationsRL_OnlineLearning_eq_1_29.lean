-- Prove2me | Theorems.Thm_FoundationsRL_OnlineLearning_eq_1_29
-- name    : FoundationsRL.OnlineLearning.eq_1_29
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:27.098677+00:00
-- url     : https://prove2.me/theorems/bfce7f1d-c922-4dd3-b53b-b9265ddba40e
-- title:
--   (1.29) — the final potential is at most the log loss of any expert
-- statement:
--   Let $\mathcal F$ be a finite class of conditional densities. For any $f^\star\in\mathcal F$,
--   $$
--   \Phi^T_1\le\sum_{i=1}^T\ell_{\log}(f^\star(x^i),y^i).
--   $$
--
--   Together with $\Phi^0_1=-\log|\mathcal F|$ and (1.28), this gives the log-loss regret bound.
--
--   **Formalization Note** Values lie in `EReal`. If $f^\star$ has zero density at some round, the right side is $+\infty$.
--
--   Differences from the source:
--   - generalization: f(·|x) a density on Y → f : X → Y → ℝ any nonnegative function; reason: the argument uses only nonnegativity, and densities are nonnegative functions
--   - encoding: ℓ_log = −log f(y|x), exp{−∑ℓ_log} → values in EReal with −log 0 = +∞, and weights written as the likelihood product; reason: a zero density has infinite loss, and exp(−∞) = 0 makes the two weight formulas agree
--   - encoding: rounds t = 1, …, T → 0-based rounds in Finset.range T; reason: Lean convention; same instances
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (1.29), p. 17

import Mathlib
import Definitions.Def_FoundationsRL_OnlineLearning_Losses
import Definitions.Def_FoundationsRL_OnlineLearning_LogLossWeights

namespace FoundationsRL.OnlineLearning

/-- **(1.29) (the final log-loss potential is at most the loss of any expert).** Foster & Rakhlin,
Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (1.29), p. 17.

For any `f⋆ ∈ F`, `Φ^T_1 ≤ ∑_{i=1}^T ℓ_log(f⋆(x^i), y^i)`.

**Formalization Note.** Values are in `EReal`. If `f⋆` has zero density at a round the right side is
`+∞`, which is why the bound holds with no positivity assumption on the densities. -/
theorem eq_1_29 {X Y : Type*} (F : Finset (X → Y → ℝ)) (hF : ∀ f ∈ F, ∀ x y, 0 ≤ f x y)
    (fstar : X → Y → ℝ) (hfstar : fstar ∈ F) (x : ℕ → X) (y : ℕ → Y) (T : ℕ) :
    logPotential F x y T ≤ ∑ i ∈ Finset.range T, logLoss (fstar (x i)) (y i) := by sorry

end FoundationsRL.OnlineLearning
