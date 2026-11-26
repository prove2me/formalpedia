-- Prove2me | Theorems.Thm_LefebvreVariations_maxent_majorization_lp_le_three
-- name    : LefebvreVariations.maxent_majorization_lp_le_three
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:38:10.516273+00:00
-- url     : https://prove2.me/theorems/9c2a7524-1ab9-4108-8684-b497ebe3033a
-- title:
--   Lefebvre's variations, No. 239 — on a theme by Li and Xie: the sorted vector solves the two majorization-constrained linear programs for dimension at most three
-- statement:
--   Let $d\le 3$, let $\lambda_1\ge\dots\ge\lambda_d\ge 0$ and $0\le\beta_1\le\dots\le\beta_d$ be real numbers.
--
--   (i) Let $F_\lambda$ be the set of $\theta\in\mathbb R^d_{\ge0}$ with $\theta_1\ge\dots\ge\theta_d$, $\sum_{i\le t}\theta_i\le\sum_{i\le t}\lambda_i$ for $1\le t\le d-1$, and $\sum_i\theta_i=\sum_i\lambda_i$. Then $\lambda\in F_\lambda$ and
--   $$
--   \sum_{i}\lambda_i\beta_i\ \le\ \sum_i\theta_i\beta_i\qquad\text{for all }\theta\in F_\lambda .
--   $$
--
--   (ii) Let $F_\beta$ be the set of $\theta\in\mathbb R^d_{\ge0}$ with $\theta_1\le\dots\le\theta_d$, $\sum_{i> t}\theta_i\le\sum_{i> t}\beta_i$ for $1\le t\le d-1$, and $\sum_i\theta_i=\sum_i\beta_i$. Then $\beta\in F_\beta$ and
--   $$
--   \sum_{i}\beta_i\lambda_i\ \le\ \sum_i\theta_i\lambda_i\qquad\text{for all }\theta\in F_\beta .
--   $$
--
--   These are the two majorization-constrained linear programs that appear in the analysis of best principal submatrix selection for the maximum entropy sampling problem: the sorted vector is an optimal solution of each. The platform lists the statement as open for every dimension $d$; here only $d\le3$ is claimed.
--
--   **Formalization Note** Vectors are `Fin d → ℝ` with 0-based indices. The prefix `{i ≤ t}` of the text is `i.val < t` and the suffix `{i > t}` is `t ≤ i.val`, for `1 ≤ t ≤ d - 1` (an empty range of `t` when `d ≤ 1`). Order hypotheses are `Antitone` and `Monotone`. Optimality means that the objective at the sorted vector is at most the objective at every feasible `θ`. The only change from the platform statement is the added hypothesis `d ≤ 3`.
--
--   **Why this is a variation.** A variation on the open platform problem MaxEntSampling.lemma_11 (the sorted vectors solve the programs (24) and (25) of the best-principal-submatrix analysis), played at d <= 3 with the parent's formal statement copied verbatim apart from the added hypothesis. The statement for all d remains open on the platform; it follows for every d from a short Abel-summation argument, but that argument is not a formal link.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Y. Li and W. Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537, Lemma 11 (programs (24) and (25)), as recorded by the platform and not re-read. The case d <= 3 was additionally checked by randomized search (200000 draws of lambda, beta and feasible theta with d in {1, 2, 3}, no violation), and follows for every d by Abel summation: the objective of (i) is beta_d times the common total minus a nonnegative combination of prefix sums of theta, and similarly for (ii).

import Mathlib

open Finset

namespace LefebvreVariations

/-- The two majorization-constrained linear programs of the best-principal-submatrix problem for
maximum entropy sampling, at dimension `d ≤ 3`. Given `λ₁ ≥ ⋯ ≥ λ_d ≥ 0` and `0 ≤ β₁ ≤ ⋯ ≤ β_d`:
the sorted vector `λ` is feasible and optimal for `min Σ θᵢ βᵢ` over nonnegative nonincreasing `θ`
whose prefix sums are at most those of `λ` with equal total, and `β` is feasible and optimal for
`min Σ θᵢ λᵢ` over nonnegative nondecreasing `θ` whose suffix sums are at most those of `β` with
equal total. For every `d` this follows from Abel summation (the objective is a nonnegative
combination of suffix, respectively prefix, sums of `θ`); the platform lists the general lemma as
open. Source: Li and Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling
Problem*, arXiv:2001.08537, Lemma 11, as recorded by the platform (not read). -/
theorem maxent_majorization_lp_le_three {d : ℕ} (hd : d ≤ 3) (lam β : Fin d → ℝ)
    (hlam : Antitone lam) (hlam0 : ∀ i, 0 ≤ lam i)
    (hβ : Monotone β) (hβ0 : ∀ i, 0 ≤ β i) :
    (lam ∈ {θ : Fin d → ℝ | (∀ i, 0 ≤ θ i) ∧ Antitone θ ∧
        (∀ t : ℕ, 1 ≤ t → t ≤ d - 1 →
          ∑ i ∈ univ.filter (fun i : Fin d => i.val < t), θ i ≤
            ∑ i ∈ univ.filter (fun i : Fin d => i.val < t), lam i) ∧
        ∑ i, θ i = ∑ i, lam i} ∧
      ∀ θ ∈ {θ : Fin d → ℝ | (∀ i, 0 ≤ θ i) ∧ Antitone θ ∧
        (∀ t : ℕ, 1 ≤ t → t ≤ d - 1 →
          ∑ i ∈ univ.filter (fun i : Fin d => i.val < t), θ i ≤
            ∑ i ∈ univ.filter (fun i : Fin d => i.val < t), lam i) ∧
        ∑ i, θ i = ∑ i, lam i},
        ∑ i, lam i * β i ≤ ∑ i, θ i * β i) ∧
    (β ∈ {θ : Fin d → ℝ | (∀ i, 0 ≤ θ i) ∧ Monotone θ ∧
        (∀ t : ℕ, 1 ≤ t → t ≤ d - 1 →
          ∑ i ∈ univ.filter (fun i : Fin d => t ≤ i.val), θ i ≤
            ∑ i ∈ univ.filter (fun i : Fin d => t ≤ i.val), β i) ∧
        ∑ i, θ i = ∑ i, β i} ∧
      ∀ θ ∈ {θ : Fin d → ℝ | (∀ i, 0 ≤ θ i) ∧ Monotone θ ∧
        (∀ t : ℕ, 1 ≤ t → t ≤ d - 1 →
          ∑ i ∈ univ.filter (fun i : Fin d => t ≤ i.val), θ i ≤
            ∑ i ∈ univ.filter (fun i : Fin d => t ≤ i.val), β i) ∧
        ∑ i, θ i = ∑ i, β i},
        ∑ i, β i * lam i ≤ ∑ i, θ i * lam i) := by
  sorry

end LefebvreVariations
