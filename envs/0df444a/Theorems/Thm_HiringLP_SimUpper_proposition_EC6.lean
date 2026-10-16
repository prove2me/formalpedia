-- Prove2me | Theorems.Thm_HiringLP_SimUpper_proposition_EC6
-- name    : HiringLP.SimUpper.proposition_EC6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:10.23297+00:00
-- url     : https://prove2.me/theorems/ee9a9d0e-c577-4a0e-84d6-43e84fd39fef
-- title:
--   Proposition EC.6, p. ec22 — s*_α = s*_β iff τ ≤ 1 − e^{−k} Σ_{j<k} k^j/j!, which holds for all k when τ ≤ 1/2
-- statement:
--   Let $k \ge 1$ be an integer and $\tau \in (0,1)$, and let $s^*_\alpha \in [0,1]$ and $s^*_\beta \in [0, \infty)$ be optimal solutions of $\alpha^\tau_k = \sup_{0 \le s \le 1} f(s)$ and $\beta^\tau_k = \sup_{s \ge 0} f(s)$, with $f(s) = s - s/\tau + \mathbb{E}[\min\{\mathrm{Pois}(sk), k\}]/(\tau k)$. Then
--   $$
--   s^*_\alpha = s^*_\beta \iff \tau \le 1 - e^{-k} \sum_{j=0}^{k-1} \frac{k^j}{j!},
--   $$
--   and the condition on the right holds whenever $\tau \le 1/2$.
--
--   The right-hand side is $\Pr[\mathrm{Pois}(k) \ge k]$; in the region it describes, the guarantee $\alpha^\tau_k$ of Theorem 3 equals the bound $\beta^\tau_k$ of Theorem 4, so value-ordered policies cannot do better than the paper's algorithm there.
--
--   **Formalization Note.** The page writes "$k \in \mathbb{N}$"; at $k = 0$ the objective divides by $0$, so $k \ge 1$ is assumed. The optimal solutions are hypotheses (their existence is part of Proposition EC.5).
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, App. D.8, p. ec22 (PDF p. 54), Proposition EC.6

import Mathlib
import Definitions.Def_HiringLP_SimUpper_Constants

namespace HiringLP.SimUpper

open Finset

/-- Proposition EC.6 (p. ec22): for `k ≥ 1` and `τ ∈ (0, 1)`, and optimal solutions `s*_α` of
`α^τ_k` and `s*_β` of `β^τ_k`, `s*_α = s*_β` iff `τ ≤ 1 − e^{−k} Σ_{i<k} k^i / i!`; this
condition holds whenever `τ ≤ 1/2`. -/
theorem proposition_EC6 (k : ℕ) (hk : 1 ≤ k) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (sα sβ : ℝ) (hα : sα ∈ Set.Icc (0 : ℝ) 1) (hαmax : IsMaxOn (HiringLP.SimLower.ratioObj k τ) (Set.Icc 0 1) sα)
    (hβ : sβ ∈ Set.Ici (0 : ℝ)) (hβmax : IsMaxOn (HiringLP.SimLower.ratioObj k τ) (Set.Ici 0) sβ) :
    (sα = sβ ↔
        τ ≤ 1 - Real.exp (-(k : ℝ)) * ∑ i ∈ range k, (k : ℝ) ^ i / (i.factorial : ℝ)) ∧
    (τ ≤ 1 / 2 →
        τ ≤ 1 - Real.exp (-(k : ℝ)) * ∑ i ∈ range k, (k : ℝ) ^ i / (i.factorial : ℝ)) := by sorry

end HiringLP.SimUpper
