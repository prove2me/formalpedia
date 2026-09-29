-- Prove2me | Theorems.Thm_LesHouchesWidth_wick_theorem
-- name    : LesHouchesWidth.wick_theorem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:19:29.502269+00:00
-- url     : https://prove2.me/theorems/bd7edd52-09ee-4050-8444-844ca16e0987
-- title:
--   Result 2: Wick's theorem for centered Gaussian vectors
-- statement:
--   Let $z\in\mathbb R^d$ be a centered Gaussian vector with positive semidefinite covariance matrix $K$, $z\sim\mathcal N(0,K)$. Then:
--
--   1. for every $m\ge0$ and indices $\mu_1,\dots,\mu_{2m}\in\{1,\dots,d\}$,
--   $$\mathbb E\big[z_{\mu_1}\cdots z_{\mu_{2m}}\big]=\sum_{\text{pairings }P\text{ of }\{1,\dots,2m\}}\ \prod_{\{k,k'\}\in P}K_{\mu_k\mu_{k'}};$$
--   2. for every $m\ge0$ and indices $\mu_1,\dots,\mu_{2m+1}$, $\mathbb E[z_{\mu_1}\cdots z_{\mu_{2m+1}}]=0$.
--
--   This reduces all moments of a Gaussian vector to its covariance. The lectures use it to compute finite-width correlators of deep linear networks.
--
--   **Formalization Note** A pairing is encoded as a fixed-point-free involution $\pi$ of $\{0,\dots,2m-1\}$, and the product runs over the $k$ with $k<\pi(k)$.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 11, Result 2, eq. (44) (Lecture 2, Section 2.2).

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem wick_theorem {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.PosSemidef) :
    (∀ (m : ℕ) (μs : Fin (2 * m) → Fin d),
      ∫ z, ∏ k, z (μs k) ∂(multivariateGaussian 0 K) =
        ∑ π ∈ pairings (2 * m),
          ∏ k ∈ Finset.univ.filter (fun k => k < π k), K (μs k) (μs (π k))) ∧
    (∀ (m : ℕ) (μs : Fin (2 * m + 1) → Fin d),
      ∫ z, ∏ k, z (μs k) ∂(multivariateGaussian 0 K) = 0) := by sorry

end LesHouchesWidth
