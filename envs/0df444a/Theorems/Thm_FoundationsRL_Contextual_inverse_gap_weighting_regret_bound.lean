-- Prove2me | Theorems.Thm_FoundationsRL_Contextual_inverse_gap_weighting_regret_bound
-- name    : FoundationsRL.Contextual.inverse_gap_weighting_regret_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T04:59:58.033454+00:00
-- url     : https://prove2.me/theorems/384d7c6c-c535-48e1-892d-be94e7ebefe1
-- title:
--   Proposition 9 — Inverse Gap Weighting estimation-to-regret inequality
-- statement:
--   This is **Proposition 9** (Foster & Rakhlin, *Foundations of Reinforcement Learning and
--   Interactive Decision Making*, p. 49-50), the Inverse Gap Weighting estimation-to-regret
--   inequality — described in the source as "the following fundamental technical result" that
--   "will be at the core of the development for the rest of the course."
--
--   Let $\Pi = \{1,\dots,A\}$ be a finite decision space. For any vector of estimated values
--   $\hat f \in \mathbb{R}^A$ and any exploration parameter $\gamma > 0$, let
--   $p = \mathrm{IGW}_\gamma(\hat f)$ be the Inverse Gap Weighting distribution of Definition 4.
--   Then for **every** vector $f^\star \in \mathbb{R}^A$, writing
--   $\pi^\star = \arg\max_\pi f^\star(\pi)$,
--
--   $$
--   \mathbb{E}_{\pi \sim p}\bigl[f^\star(\pi^\star) - f^\star(\pi)\bigr] \le
--   \frac{A}{\gamma} + \gamma \cdot \mathbb{E}_{\pi \sim p}\bigl[(\hat f(\pi) - f^\star(\pi))^2\bigr].
--   $$
--
--   The left-hand side is the instantaneous regret of sampling $\pi \sim p$ against the best
--   action under $f^\star$; the right-hand side is an exploration cost $A/\gamma$ plus $\gamma$
--   times the estimation error of $\hat f$ relative to $f^\star$ under $p$. The inequality holds
--   for *any* estimator $\hat f$ and *any* ground-truth $f^\star$, independent of any model class
--   or problem structure — it is a purely algebraic property of the IGW sampling rule. This is
--   the mechanism that converts a bound on estimation error (supplied by an online or offline
--   regression oracle) into a bound on decision-making regret, and underlies the SquareCB
--   algorithm (Proposition 10).
--
--   **Formalization Note** The inequality is stated with the exact constants ($A/\gamma$ and
--   $\gamma$, with no hidden multiplicative slack) that the book's own proof establishes; the
--   source states the result without a $\lesssim$, so no approximation is introduced here either.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 49-50, Proposition 9 (Eq. 3.37)

import Mathlib
import Definitions.Def_FoundationsRL_Contextual_IsIGW

namespace FoundationsRL.Contextual

/-- Proposition 9 (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
Decision Making*, arXiv:2312.16730v1, p. 49-50): the Inverse Gap Weighting
estimation-to-regret inequality. For any vector of estimated values `fhat : Fin A → ℝ`,
exploration parameter `γ > 0`, and distribution `p` satisfying `IsIGW A fhat γ bstar p`, the
inequality holds for every ground-truth vector `fstar : Fin A → ℝ` with optimal action
`pistar`. -/
theorem inverse_gap_weighting_regret_bound {A : ℕ} (fhat fstar : Fin A → ℝ) (γ : ℝ)
    (hγ : 0 < γ) (bstar : Fin A) (pistar : Fin A) (hpistar : ∀ π, fstar π ≤ fstar pistar)
    (p : Fin A → ℝ) (hp : IsIGW A fhat γ bstar p) :
    fstar pistar - ∑ π, p π * fstar π ≤ (A : ℝ) / γ + γ * ∑ π, p π * (fhat π - fstar π) ^ 2 := by sorry

end FoundationsRL.Contextual
