-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_lemma_2_10
-- name    : LpSubspaceCoreset.SmallP.lemma_2_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:48:09.071706+00:00
-- url     : https://prove2.me/theorems/394ee76a-d591-479d-b9b3-ef0cb2bf358b
-- title:
--   Lemma 2.10 — Cohen–Peng iteration
-- statement:
--   Fix $1\le p<2$ and the factor $\beta\ge1$ of the constant-factor leverage-score approximations used in line 4 of Algorithm 1. There are constants $C>0$ and $\alpha\ge1$, depending only on $p$ and $\beta$, such that for every $M\in\mathbb R^{N\times r}$ of full column rank, every admissible choice of the approximations $\tau^{(t)}$ and every
--   $$T\ge C\log\log(N+2),$$
--   the vector $w^{(T)}$ returned by Algorithm 1 after $T$ iterations is an $\alpha$-approximation to the ℓp Lewis weights of $M$.
--
--   It is how Proposition 4.1 computes the Lewis weights of the low-rank part.
--
--   Differences from the source:
--   - reading: τ a constant-factor approximation of the leverage scores; T = O_p(log log(N + 2)); w a constant-factor approximation → ∀ β ≥ 1 ∃ C, α: every β-approximate sequence τ and every T ≥ C·log log(N + 2) give an α-approximation; reason: constants fixed before the instance; every iteration count above the bound (the iteration is a contraction, more rounds do not hurt)
--   - encoding: the Lewis weights of M → every w with IsLewisWeights p M w; reason: unique by Eq. (2.4)
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 11, Lemma 2.10 and Algorithm 1

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Lewis

namespace LpSubspaceCoreset.SmallP

/-- **Lemma 2.10** (Cohen–Peng iteration [CP15]), p. 11.

Fix `1 ≤ p < 2` and the factor `β ≥ 1` of the constant-factor leverage-score approximations used
in line 4 of Algorithm 1. There are constants `C > 0` and `α ≥ 1` (depending only on `p` and `β`)
such that for every `M ∈ ℝ^{N×r}` of full column rank, every admissible sequence of leverage-score
approximations, and every `T ≥ C·log log(N + 2)`, the vector `w` returned by Algorithm 1 after `T`
iterations is an `α`-approximation to the ℓp Lewis weights of `M`. -/
theorem lemma_2_10 :
    ∀ p : ℝ, 1 ≤ p → p < 2 → ∀ β : ℝ, 1 ≤ β →
    ∃ C α : ℝ, 0 < C ∧ 1 ≤ α ∧
    ∀ (N r : ℕ) (M : Matrix (Fin N) (Fin r) ℝ), M.rank = r →
    ∀ τ : ℕ → Fin N → ℝ, IsCPChoice p β M τ →
    ∀ T : ℕ, C * Real.log (Real.log ((N : ℝ) + 2)) ≤ T →
    ∀ w : Fin N → ℝ, IsLewisWeights p M w → IsApproxLewis α (cohenPeng p τ T) w := by sorry

end LpSubspaceCoreset.SmallP
