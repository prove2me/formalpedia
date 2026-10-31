-- Prove2me | Theorems.Thm_FoundationsRL_OnlineLearning_eq_1_28
-- name    : FoundationsRL.OnlineLearning.eq_1_28
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:57.492998+00:00
-- url     : https://prove2.me/theorems/a8683dbe-39c3-40d4-96dc-db2300fbb5cd
-- title:
--   (1.28) — log-loss increment: $\ell_{\log}(\hat f^t(x^t),y^t)=\Phi^t_1-\Phi^{t-1}_1$
-- statement:
--   Let $\mathcal F$ be a finite class of conditional densities. With $\eta=1$, the averaged variant of Exponential Weights predicts the mixture $\hat f^t(y\mid x)=\sum_{f\in\mathcal F}q^t(f)f(y\mid x)$, and at each round for which $q^t$ is defined,
--   $$
--   \ell_{\log}(\hat f^t(x^t),y^t)=-\log\hat f^t(y^t\mid x^t)=\Phi^t_1-\Phi^{t-1}_1.
--   $$
--
--   The loss on each round is exactly the change in potential, which is what makes the log-loss regret telescope.
--
--   **Formalization Note** Values lie in `EReal`. $q^t$ is defined when the likelihoods of the past do not all vanish. The new potential may still be $+\infty$, and then so is the loss.
--
--   Differences from the source:
--   - generalization: f(·|x) a density on Y → f : X → Y → ℝ any nonnegative function; reason: the argument uses only nonnegativity, and densities are nonnegative functions
--   - encoding: ℓ_log = −log f(y|x), exp{−∑ℓ_log} → values in EReal with −log 0 = +∞, and weights written as the likelihood product; reason: a zero density has infinite loss, and exp(−∞) = 0 makes the two weight formulas agree
--   - encoding: (1.28) stated without condition → 0 < ∑ f ∈ F, likelihood f x y t; reason: this only says q^t is defined; otherwise (1.27) is 0/0 and the right side is ⊤ − ⊤
--   - encoding: rounds t = 1, …, T → 0-based rounds in Finset.range T; reason: Lean convention; same instances
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (1.27)–(1.28), p. 16

import Mathlib
import Definitions.Def_FoundationsRL_OnlineLearning_Losses
import Definitions.Def_FoundationsRL_OnlineLearning_ExponentialWeights
import Definitions.Def_FoundationsRL_OnlineLearning_LogLossWeights

namespace FoundationsRL.OnlineLearning

/-- **(1.28) (the log-loss potential telescopes).** Foster & Rakhlin, Foundations of Reinforcement
Learning and Interactive Decision Making, arXiv:2312.16730v1, (1.28), p. 16.

With `η = 1`, the averaged prediction satisfies `ℓ_log(f̂^t(x^t), y^t) = Φ^t_1 - Φ^{t-1}_1`.

**Formalization Note.** Rounds are 0-based, so the notes' `t` is `t + 1` here. Values are in `EReal`.
The hypothesis `ht` says that `q^t` is defined, that is, its denominator in (1.27) is positive. Without
it the right side would be `⊤ - ⊤`. The new potential may still be `+∞`, in which case so is the loss. -/
theorem eq_1_28 {X Y : Type*} (F : Finset (X → Y → ℝ)) (hF : ∀ f ∈ F, ∀ x y, 0 ≤ f x y)
    (x : ℕ → X) (y : ℕ → Y) (t : ℕ) (ht : 0 < ∑ f ∈ F, likelihood f x y t) :
    logLoss (ewAveraged F (logDist F x y t) (x t)) (y t) =
      logPotential F x y (t + 1) - logPotential F x y t := by sorry

end FoundationsRL.OnlineLearning
