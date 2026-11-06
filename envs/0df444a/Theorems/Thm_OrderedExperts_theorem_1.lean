-- Prove2me | Theorems.Thm_OrderedExperts_theorem_1
-- name    : OrderedExperts.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:35:59.476376+00:00
-- url     : https://prove2.me/theorems/ea33544a-aa15-403d-b3a7-2504f47284ca
-- title:
--   Theorem 1 — endpoint flow estimator
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $\pi$ satisfy the floor $\pi(j)\ge\xi/m$ on the active ranks $1,\dots,m$ ($0<\xi\le1$, $\sum_j\pi(j)=1$) and $\Lambda=1+\log(m/\xi)$. Draw $A\sim\pi$ and then $B\sim\kappa(A,\cdot)$ (Algorithm 1, so $\mathbb P(A=a,B=b)=\pi(a)\kappa(a,b)$, a law depending only on $\pi$), and let $\hat g$ be the endpoint flow estimate, which depends on $g$ only through $g(x_A)$ and $g(x_B)$. For every hidden vector $g$ with values in $[0,1]$ and $\mathrm{TV}(g)=\sum_{j=2}^m|g(x_j)-g(x_{j-1})|\le1$:
--   1. the pair law is a probability law with marginals $A\sim\pi$ and $B\sim\pi$;
--   2. unbiasedness: $\mathbb E[\hat g(j)]=g(x_j)$ for every target $j$;
--   3. second moment: $\mathbb E\langle\pi,\hat g^2\rangle\le C\Lambda^2$;
--   4. self-bound: for every realization, $\max_j\pi(j)|\hat g(j)|\le3\Lambda$;
--   5. monotone sign: if $g$ is nondecreasing, then $\hat g(j)\ge0$ for every $j$ and every realization.
--
--   This is the estimator behind the paper's two-point algorithms: both queried actions are played with the intended marginal, and the whole loss vector is reconstructed unbiasedly with logarithmic second moment.
--
--   Differences from the source:
--   - reading: there exist a random pair whose law depends only on $\pi$ and an estimator depending on $g$ only through $g(x_A),g(x_B)$ → the pair of Algorithm 1 and the endpoint flow estimate of Sec. 3.3; reason: the theorem's witnesses are the construction of Sec. 3.3, used by Theorem 2; the Lean statement implies the printed existential
--   - encoding: $O(\Lambda^2)$ → one absolute constant $C>0$ chosen before $m$, $\xi$, $\pi$, $g$; reason: meaning of $O(\cdot)$ in the paper
--   - encoding: expectations and marginals of a random pair; every realization → finite sums against $\pi(a)\kappa(a,b)$; every pair of active ranks; reason: finite probability space; same instances
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Theorem 1, p.6; Sec. 3.3, pp.8–9; Algorithm 1, p.9

import Definitions.Def_OrderedExperts_est
import Definitions.Def_OrderedExperts_kappa
import Definitions.Def_OrderedExperts_IsFloored
open Finset

namespace OrderedExperts

/-- **Theorem 1 (Endpoint flow estimator).** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Theorem 1, p.6: "Let `π`
satisfy the floor `π(j) ≥ ξ/m`. There exist a random pair of ranks `(A, B)`, whose law depends only on
`π`, and an estimator `ĝ`, which depends on `g` only through the observed values `g(xA)` and `g(xB)`,
such that for every hidden vector `g` with values in `[0, 1]` and `TV(g) ≤ 1`: 1. marginals: `A ∼ π` and
`B ∼ π`; 2. unbiasedness: `E[ĝ(j)] = g(xj)` for every target `j`; 3. second moment:
`E⟨π, ĝ²⟩ = O(Λ²)`; 4. self-bound: for every realization, `max_j π(j)|ĝ(j)| ≤ 3Λ`; 5. monotone sign: if
`g` is nondecreasing, then `ĝ(j) ≥ 0` for every `j` and every realization."

The pair is the one of Algorithm 1 (law `π(a)κ(a, b)`) and the estimator is the endpoint-flow
estimate `est`. There is an absolute constant `C > 0` such that, under the floor, for every `g` with
values in `[0, 1]` on the active ranks and `TV(g) ≤ 1`: the pair law is a probability law on
`{1, …, m}²` with both marginals `π`; `est` is unbiased; `E Σ_j π(j) ĝ(j)² ≤ CΛ²`; every realization
satisfies `π(j)|ĝ(j)| ≤ 3Λ`; and if `g` is nondecreasing every realization of `ĝ` is nonnegative.

**Formalization Note.** The existential "there exist a random pair and an estimator" is stated for
the paper's construction (Sec. 3.3, Algorithm 1), which implies it; the law depends only on `π` and
`est` reads `g` only at `A` and `B` by definition. `O(Λ²)` is one absolute constant, quantified before
`m`, `ξ`, `π`, `g`. -/
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (ξ : ℝ) (π g : ℕ → ℝ), IsFloored m ξ π →
      (∀ j ∈ Icc 1 m, 0 ≤ g j ∧ g j ≤ 1) → ∑ j ∈ Icc 2 m, |g j - g (j - 1)| ≤ 1 →
      ((∀ a ∈ Icc 1 m, ∀ b ∈ Icc 1 m, 0 ≤ π a * kappa m ξ π a b) ∧
          ∑ a ∈ Icc 1 m, ∑ b ∈ Icc 1 m, π a * kappa m ξ π a b = 1) ∧
      ((∀ a ∈ Icc 1 m, ∑ b ∈ Icc 1 m, π a * kappa m ξ π a b = π a) ∧
          (∀ b ∈ Icc 1 m, ∑ a ∈ Icc 1 m, π a * kappa m ξ π a b = π b)) ∧
      (∀ j ∈ Icc 1 m,
          ∑ a ∈ Icc 1 m, ∑ b ∈ Icc 1 m, π a * kappa m ξ π a b * est m ξ π g a b j = g j) ∧
      (∑ a ∈ Icc 1 m, ∑ b ∈ Icc 1 m,
          π a * kappa m ξ π a b * ∑ j ∈ Icc 1 m, π j * est m ξ π g a b j ^ 2 ≤
        C * bigLambda m ξ ^ 2) ∧
      (∀ a ∈ Icc 1 m, ∀ b ∈ Icc 1 m, ∀ j ∈ Icc 1 m,
          π j * |est m ξ π g a b j| ≤ 3 * bigLambda m ξ) ∧
      (MonotoneOn g (Icc 1 m : Set ℕ) →
          ∀ a ∈ Icc 1 m, ∀ b ∈ Icc 1 m, ∀ j ∈ Icc 1 m, 0 ≤ est m ξ π g a b j) := by sorry

end OrderedExperts
