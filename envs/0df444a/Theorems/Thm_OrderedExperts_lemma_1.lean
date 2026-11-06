-- Prove2me | Theorems.Thm_OrderedExperts_lemma_1
-- name    : OrderedExperts.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:34:22.507771+00:00
-- url     : https://prove2.me/theorems/0709f947-dc86-4dcb-b387-713c75bddddd
-- title:
--   Lemma 1 — unbiased importance-weighted flow estimator
-- statement:
--   Let $P$ be a probability law of the queried pair $(A,B)$ on the active ranks $\{1,\dots,m\}^2$, with revelation probabilities $q(0,a)=\mathbb P(A=a)$ and $q(a,b)=P(a,b)+P(b,a)$ ($a<b$). Let $\varphi_j(e)\ge0$ be flows and $g$ a hidden vector with $g(x_0)=0$, and fix a target $j\in\{1,\dots,m\}$ such that
--   1. $q(e)>0$ whenever $\varphi_j(e)>0$, for all anchor edges $(0,a)$ and interval edges $(a,b)$, $1\le a<b\le m$;
--   2. the flow identity holds: $g(x_j)=\sum_{a}\varphi_j(0,a)\,g(x_a)+\sum_{1\le a<b\le m}\varphi_j(a,b)\bigl(g(x_b)-g(x_a)\bigr)$.
--
--   Let $\hat g(j)$ be the importance-weighted estimator, which weights each revealed increment by $\varphi_j(e)/q(e)$ (sums over edges with $q>0$). Then
--   $$
--   \mathbb E\,\hat g(j)=g(x_j).
--   $$
--   Moreover, if $g$ is nonnegative and nondecreasing on the chain, then $\hat g(j)\ge0$ for every realization $(A,B)$.
--
--   The estimator is unbiased for every target simultaneously from two observations, for any law of the queried pair; Theorem 1 instantiates it with the reversible pair sampler.
--
--   **Formalization Note** The expectation is the finite sum $\sum_{A,B}P(A,B)\hat g(j)$.
--
--   Differences from the source:
--   - generalization: flows are the edge-use probabilities of a random increasing path to $j$ (Sec. 3.2) → any nonnegative $\varphi$ satisfying the flow identity for $g$ at $j$; reason: path flows are nonnegative and satisfy the identity $g(x_j)=\sum_e\varphi_j(e)H(e)$ (p.7), so the statement specializes to the source
--   - generalization: support condition and flow identity for every target $j$ → only at the target $j$ considered; reason: the conclusion at $j$ uses only those at $j$; quantifying over all $j$ recovers the source
--   - encoding: a random pair with a law; expectation → a law $P$ on $\{1,\dots,m\}^2$ given by its point masses; the finite sum $\sum_{A,B}P(A,B)\hat g(j)$; reason: finite probability space; same instances
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Lemma 1, p.8; Sec. 3.2, p.7

import Definitions.Def_OrderedExperts_genEst
open Finset

namespace OrderedExperts

/-- **Lemma 1 (Unbiased estimator).** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Lemma 1, p.8: "Suppose that `q(e) > 0`
whenever `φj(e) > 0`, and define `ĝ(j) = Σ_a 1{E1 = (0, a)} φj(0, a)/q(0, a) H(0, a) +
Σ_{1≤a<b} 1{E2 = (a, b)} φj(a, b)/q(a, b) H(a, b)`, where the sums run over edges with `q > 0`. Then
`Eĝ(j) = g(xj)` for every `j`. If `g` is nonnegative and nondecreasing, then `ĝ(j) ≥ 0` for every `j`
and every realization." The flows satisfy "`g(xj) = Σ_e φj(e)H(e)`" (Sec. 3.2, p.7), and the
subsection "works for any law of the queried pair".

For any probability law `P` of the queried pair on `{1, …, m}²`, nonnegative flows `φ`, a target
`j ∈ {1, …, m}` at which the support condition and the flow identity hold, the expectation of
`genEst m P φ g A B j` under `P` is `g j`; and if `g` is nonnegative and nondecreasing on the chain,
every realization of `genEst` is nonnegative.

**Formalization Note.** `g(x0) = 0` is built into `genEst`. The flows are any nonnegative numbers
satisfying the flow identity for `g` at `j`, which every random increasing path satisfies. -/
theorem lemma_1 (m : ℕ) (P : ℕ → ℕ → ℝ) (hP : ∀ a ∈ Icc 1 m, ∀ b ∈ Icc 1 m, 0 ≤ P a b)
    (hP1 : ∑ a ∈ Icc 1 m, ∑ b ∈ Icc 1 m, P a b = 1)
    (φ : ℕ → ℕ → ℕ → ℝ) (hφ : ∀ j a b, 0 ≤ φ j a b) (g : ℕ → ℝ) (j : ℕ) (hj : j ∈ Icc 1 m)
    (hsupp0 : ∀ a ∈ Icc 1 m, 0 < φ j 0 a → 0 < revAnchor m P a)
    (hsuppI : ∀ a ∈ Icc 1 m, ∀ b ∈ Ioc a m, 0 < φ j a b → 0 < revInterval P a b)
    (hflow : g j = ∑ a ∈ Icc 1 m, φ j 0 a * g a +
      ∑ a ∈ Icc 1 m, ∑ b ∈ Ioc a m, φ j a b * (g b - g a)) :
    ∑ A ∈ Icc 1 m, ∑ B ∈ Icc 1 m, P A B * genEst m P φ g A B j = g j ∧
    ((∀ a ∈ Icc 1 m, 0 ≤ g a) → MonotoneOn g (Icc 1 m : Set ℕ) →
      ∀ A ∈ Icc 1 m, ∀ B ∈ Icc 1 m, 0 ≤ genEst m P φ g A B j) := by sorry

end OrderedExperts
