-- Prove2me | Theorems.Thm_HiringLP_SimUpper_proposition_EC5
-- name    : HiringLP.SimUpper.proposition_EC5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:08.839923+00:00
-- url     : https://prove2.me/theorems/3b6abc20-4bb0-443f-946d-5c962cc7a14e
-- title:
--   Proposition EC.5, p. ec20 — s*_α = min{s*_β, 1}, and s*_β solves τ = 1 − e^{−sk} Σ_{j<k} (sk)^j/j!
-- statement:
--   Let $k \ge 1$ be an integer, $\tau \in (0,1)$, and $f(s) = s - s/\tau + \mathbb{E}[\min\{\mathrm{Pois}(sk), k\}]/(\tau k)$ the objective defining $\alpha^\tau_k = \sup_{0 \le s \le 1} f(s)$ and $\beta^\tau_k = \sup_{s \ge 0} f(s)$. Then optimal solutions $s^*_\alpha \in [0,1]$ of $\alpha^\tau_k$ and $s^*_\beta \in [0,\infty)$ of $\beta^\tau_k$ exist, and for any such optimal solutions
--   $$
--   s^*_\alpha = \min\{s^*_\beta, 1\}, \qquad \tau = 1 - e^{-s^*_\beta k} \sum_{j=0}^{k-1} \frac{(s^*_\beta k)^j}{j!}.
--   $$
--
--   The proposition characterises both maximisers by a first-order condition and explains when the lower bound $\alpha^\tau_k$ (Theorem 3) and the upper bound $\beta^\tau_k$ (Theorem 4) coincide.
--
--   **Formalization Note.** The page says "let $s^*_\alpha$ and $s^*_\beta$ be optimal solutions"; the existence of optimal solutions, which this presupposes, is stated as two explicit conjuncts so that the statement is not vacuous. The page leaves $k$ implicit; it is a positive integer here (for $k = 0$ the objective divides by $0$).
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, App. D.8, p. ec20 (PDF p. 52), Proposition EC.5

import Mathlib
import Definitions.Def_HiringLP_SimUpper_Constants

namespace HiringLP.SimUpper

open Finset

/-- Proposition EC.5 (p. ec20): for `k ≥ 1` and `τ ∈ (0, 1)`, optimal solutions `s*_α` of
`α^τ_k` (over `[0, 1]`) and `s*_β` of `β^τ_k` (over `[0, ∞)`) exist, and for any such pair
`s*_α = min{s*_β, 1}` and `τ = 1 − e^{−s*_β k} Σ_{i<k} (s*_β k)^i / i!`. -/
theorem proposition_EC5 (k : ℕ) (hk : 1 ≤ k) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (∃ s ∈ Set.Icc (0 : ℝ) 1, IsMaxOn (HiringLP.SimLower.ratioObj k τ) (Set.Icc 0 1) s) ∧
    (∃ s ∈ Set.Ici (0 : ℝ), IsMaxOn (HiringLP.SimLower.ratioObj k τ) (Set.Ici 0) s) ∧
    ∀ sα sβ : ℝ, sα ∈ Set.Icc (0 : ℝ) 1 → IsMaxOn (HiringLP.SimLower.ratioObj k τ) (Set.Icc 0 1) sα →
      sβ ∈ Set.Ici (0 : ℝ) → IsMaxOn (HiringLP.SimLower.ratioObj k τ) (Set.Ici 0) sβ →
      sα = min sβ 1 ∧
        τ = 1 - Real.exp (-(sβ * k)) * ∑ i ∈ range k, (sβ * k) ^ i / (i.factorial : ℝ) := by sorry

end HiringLP.SimUpper
