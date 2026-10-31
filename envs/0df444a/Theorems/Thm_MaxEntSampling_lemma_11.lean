-- Prove2me | Theorems.Thm_MaxEntSampling_lemma_11
-- name    : MaxEntSampling.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:57:00.153262+00:00
-- url     : https://prove2.me/theorems/705a8db4-bd38-438e-90c5-209e0dc61492
-- title:
--   Lemma 11 — sorted vectors solve the programs (24) and (25)
-- statement:
--   Let $\lambda_1\ge\cdots\ge\lambda_d\ge0$ and $0\le\beta_1\le\cdots\le\beta_d$.
--
--   1. $\lambda$ is an optimal solution of
--   $$
--   \min_{\theta\in\mathbb R^d_+,\ \theta_1\ge\cdots\ge\theta_d}\Bigl\{\sum_{i\in[d]}\theta_i\beta_i : \sum_{i\in[t]}\theta_i\le\sum_{i\in[t]}\lambda_i\ \forall t\in[d-1],\ \sum_{i\in[d]}\theta_i=\sum_{i\in[d]}\lambda_i\Bigr\}. \tag{24}
--   $$
--   2. $\beta$ is an optimal solution of
--   $$
--   \min_{\theta\in\mathbb R^d_+,\ \theta_1\le\cdots\le\theta_d}\Bigl\{\sum_{i\in[d]}\theta_i\lambda_i : \sum_{i\in[t+1,d]}\theta_i\le\sum_{i\in[t+1,d]}\beta_i\ \forall t\in[d-1],\ \sum_{i\in[d]}\theta_i=\sum_{i\in[d]}\beta_i\Bigr\}. \tag{25}
--   $$
--
--   In each part the vector is feasible and no feasible $\theta$ has a smaller objective. These linear programs bound the trace terms $\operatorname{tr}(X\Lambda)$ in the proofs of Lemmas 1 and 3 through the majorization of a diagonal by the spectrum.
--
--   **Formalization Note** Vectors are indexed by `Fin d` from $0$; $[t]$ is $i<t$, $[t+1,d]$ is $t\le i$, and $t$ ranges over $1\le t\le d-1$.
--
--   Differences from the source:
--   - reading: λ := arg min …, β := arg min … → the vector is feasible and its objective is at most that of every feasible θ; reason: the proof (p.41) shows that λ is an optimal solution; minimizers need not be unique (e.g. constant β), so arg min names one of them
--   - encoding: λ1 ≥ ··· ≥ λd ≥ 0 and 0 ≤ β1 ≤ ··· ≤ βd → Antitone lam ∧ ∀ i, 0 ≤ lam i and Monotone β ∧ ∀ i, 0 ≤ β i; reason: same vectors; 0-based indices
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, Lemma 11, p.40 (PDF p.40), proof pp.40–41

import Mathlib

open Finset

namespace MaxEntSampling

/-- **Lemma 11: sorted vectors solve the two majorization-constrained linear programs (24)–(25).**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, Lemma 11, p.40 (PDF p.40), with proof pp.40–41: given
`λ1 ≥ ··· ≥ λd ≥ 0` and `0 ≤ β1 ≤ ··· ≤ βd`,
(i) `λ` is an optimal solution of
`min { Σ_{i∈[d]} θi βi : θ ∈ ℝ^d_+, θ1 ≥ ··· ≥ θd, Σ_{i∈[t]} θi ≤ Σ_{i∈[t]} λi ∀t ∈ [d−1],
Σ_{i∈[d]} θi = Σ_{i∈[d]} λi }` (24);
(ii) `β` is an optimal solution of
`min { Σ_{i∈[d]} θi λi : θ ∈ ℝ^d_+, θ1 ≤ ··· ≤ θd, Σ_{i∈[t+1,d]} θi ≤ Σ_{i∈[t+1,d]} βi ∀t ∈ [d−1],
Σ_{i∈[d]} θi = Σ_{i∈[d]} βi }` (25).

Each part says: the vector is feasible for the program, and its objective value is at most that
of every feasible `θ`.

**Formalization Note.** Vectors are `Fin d → ℝ` with 0-based indices. `λ1 ≥ ··· ≥ λd ≥ 0` is
`Antitone lam ∧ ∀ i, 0 ≤ lam i`, `0 ≤ β1 ≤ ··· ≤ βd` is `Monotone β ∧ ∀ i, 0 ≤ β i`. The 1-based
prefix `[t]` is `i.val < t` and the suffix `[t+1, d]` is `t ≤ i.val`, for `t ∈ [d−1]`, i.e.
`1 ≤ t ≤ d − 1`. "λ := arg min" is read as "λ is a minimizer", as the proof states (p.41: "it
needs to show that the vector λ ∈ R^d_+ is an optimal solution"); minimizers need not be unique. -/
theorem lemma_11 {d : ℕ} (lam β : Fin d → ℝ) (hlam : Antitone lam) (hlam0 : ∀ i, 0 ≤ lam i)
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
        ∑ i, β i * lam i ≤ ∑ i, θ i * lam i) := by sorry

end MaxEntSampling
