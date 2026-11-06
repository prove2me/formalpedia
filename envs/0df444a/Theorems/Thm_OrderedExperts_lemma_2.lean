-- Prove2me | Theorems.Thm_OrderedExperts_lemma_2
-- name    : OrderedExperts.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:35:52.614263+00:00
-- url     : https://prove2.me/theorems/52067e2f-1da2-419c-8fca-75ed53e795a8
-- title:
--   Lemma 2 — kernel validity and detailed balance
-- statement:
--   Let $\pi$ satisfy the floor $\pi(j)\ge\xi/m$ ($0<\xi\le1$) on the active ranks $1,\dots,m$, with $\sum_j\pi(j)=1$, and let $\Lambda=1+\log(m/\xi)$, $\Gamma(a,b)=\frac{1}{4\Lambda}\frac{\pi(a)\pi(b)}{\Pi[a,b]}$ and $\kappa(b,a)=\Gamma(a,b)/\pi(b)$ ($a\ne b$), $\kappa(b,b)=1-\sum_{a\ne b}\kappa(b,a)$. Then:
--   1. $\kappa$ is a valid Markov kernel on $\{1,\dots,m\}$: all entries are nonnegative and every row sums to one;
--   2. $\kappa(b,b)\ge 1/2$ for every $b$;
--   3. detailed balance: $\pi(b)\kappa(b,a)=\pi(a)\kappa(a,b)=\Gamma(a,b)$ for $a\ne b$;
--   4. $\pi$ is stationary: $\sum_b\pi(b)\kappa(b,a)=\pi(a)$.
--
--   Drawing $A\sim\pi$ and then $B\sim\kappa(A,\cdot)$ therefore gives $B\sim\pi$ as well, so both played endpoints have the intended marginal.
--
--   Differences from the source:
--   - encoding: $\kappa$ is valid → nonnegative entries and unit row sums over the active ranks; reason: definition of a Markov kernel on a finite set
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Lemma 2, p.9; Sec. 3.3, p.8; Appendix A.2, p.17

import Definitions.Def_OrderedExperts_kappa
import Definitions.Def_OrderedExperts_IsFloored
open Finset

namespace OrderedExperts

/-- **Lemma 2 (Kernel validity).** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Lemma 2, p.9: "The kernel `κ` is valid,
in particular `κ(b, b) ≥ 1/2`, and satisfies detailed balance `π(b)κ(b, a) = π(a)κ(a, b) = Γ(a, b)`.
Hence `π` is stationary."

Under the floor of Sec. 3.1 (`IsFloored m ξ π`), the kernel `κ` on the active ranks `{1, …, m}` has
nonnegative entries and unit row sums, its diagonal is at least `1/2`, it satisfies detailed balance
with the conductance `Γ`, and `π` is stationary for it. -/
theorem lemma_2 (m : ℕ) (ξ : ℝ) (π : ℕ → ℝ) (hπ : IsFloored m ξ π) :
    (∀ b ∈ Icc 1 m, ∀ a ∈ Icc 1 m, 0 ≤ kappa m ξ π b a) ∧
    (∀ b ∈ Icc 1 m, ∑ a ∈ Icc 1 m, kappa m ξ π b a = 1) ∧
    (∀ b ∈ Icc 1 m, 1 / 2 ≤ kappa m ξ π b b) ∧
    (∀ a ∈ Icc 1 m, ∀ b ∈ Icc 1 m, a ≠ b →
      π b * kappa m ξ π b a = gamma m ξ π a b ∧ π a * kappa m ξ π a b = gamma m ξ π a b) ∧
    (∀ a ∈ Icc 1 m, ∑ b ∈ Icc 1 m, π b * kappa m ξ π b a = π a) := by sorry

end OrderedExperts
