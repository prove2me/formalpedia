-- Prove2me | Theorems.Thm_Fundraising_PartialCollab_sum_ge_alpha
-- name    : Fundraising.PartialCollab.sum_ge_alpha
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:02:36.61315+00:00
-- url     : https://prove2.me/theorems/bdb417dd-215c-465b-b1b4-7f97f40aa283
-- title:
--   Claim in the proof of Proposition 4(ii), p. S14 — solutions of the effort system satisfy Σ_i x_i ≥ α_1
-- statement:
--   Let $\alpha_1 \ge \alpha_2 \ge \dots \ge \alpha_n$ be real numbers ($n \ge 1$) and let $x_1, \dots, x_n$ be real numbers solving the effort system
--   $$x_i = \Big(\alpha_i - \sum_{j \ne i} x_j\Big)^+ \qquad \text{for all } i.$$
--   Then
--   $$\sum_{i=1}^n x_i \ge \alpha_1 .$$
--
--   This is the first step in solving the effort system of Proposition 4(ii): together with the system it pins the total effort at the largest $\alpha_i$.
--
--   **Formalization Note** Indices are $0$-based in Lean, so $\alpha_1$ is `α 0`; $(\cdot)^+$ is `max (·) 0`. The ordering hypothesis is the paper's "without loss of generality" assumption of part (ii).
-- source:
--   Aflaki, Pedraza-Martinez, Competition and Collaboration on Fundraising for Short-Term Disaster Response: The Impact on Earmarking and Performance, SSRN 3705595 (version of December 2022), p. S14 (PDF 47), proof of Proposition 4(ii), first claim

import Mathlib

namespace Fundraising.PartialCollab

open Finset

/-- Claim in the proof of Proposition 4(ii), p. S14: if `α_0 ≥ α_1 ≥ ⋯ ≥ α_{n-1}` and the
efforts solve `x_i = (α_i − Σ_{j ≠ i} x_j)^+` for every `i`, then `Σ_i x_i ≥ α_0`. -/
theorem sum_ge_alpha {n : ℕ} [NeZero n] (α x : Fin n → ℝ) (hα : Antitone α)
    (hx : ∀ i, x i = max (α i - ∑ j ∈ univ.erase i, x j) 0) :
    α 0 ≤ ∑ i, x i := by sorry

end Fundraising.PartialCollab
