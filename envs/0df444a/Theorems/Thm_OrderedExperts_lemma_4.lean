-- Prove2me | Theorems.Thm_OrderedExperts_lemma_4
-- name    : OrderedExperts.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:34:58.420246+00:00
-- url     : https://prove2.me/theorems/56cc0f7d-4c9b-4173-a573-769877b75c3e
-- title:
--   Lemma 4 — edge loads of the endpoint flow estimator
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $\pi$ satisfy the floor $\pi(j)\ge\xi/m$ on the active ranks $1,\dots,m$ ($0<\xi\le1$, $\sum_j\pi(j)=1$), let $\Lambda=1+\log(m/\xi)$, and let $q(0,a)=\pi(a)$ and $q(a,b)=2\Gamma(a,b)$ be the revelation probabilities of the pair sampler of Algorithm 1. Then for every active rank $a$,
--   $$
--   \frac{\sum_{j\ge a}\pi(j)\varphi_j(0,a)^2}{q(0,a)}\le C\,\frac{\pi(a)}{\Pi[1,a]},
--   $$
--   and for every pair of active ranks $1\le a<b\le m$,
--   $$
--   \frac{\sum_{j\ge b}\pi(j)\varphi_j(a,b)^2}{q(a,b)}\le C\,\Lambda\,\frac{\pi(a)\pi(b)}{\Pi(a,b]\,\Pi[a,b]}.
--   $$
--
--   The factor $\Lambda$ in the interval bound is the price of the kernel normalization; Lemma 5 sums these loads against the squared increments.
--
--   Differences from the source:
--   - encoding: $O(\cdot)$ → one absolute constant $C>0$ chosen before $m$, $\xi$, $\pi$; reason: meaning of $O(\cdot)$ in the paper
--   - encoding: $q(0,a)$, $q(a,b)$ of the pair → $\pi(a)$ and $2\Gamma(a,b)$; reason: the revelation probabilities of Algorithm 1's pair (p.9)
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Lemma 4, p.10; Sec. 3.3, p.9; Appendix A.4, p.18

import Definitions.Def_OrderedExperts_phi
import Definitions.Def_OrderedExperts_gamma
import Definitions.Def_OrderedExperts_massOC
import Definitions.Def_OrderedExperts_IsFloored
open Finset

namespace OrderedExperts

/-- **Lemma 4 (Edge loads).** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Lemma 4, p.10: "For every
rank `a`, `Σ_{j≥a} π(j)φj(0, a)²/q(0, a) = O(π(a)/Π[1, a])`, and for every pair of ranks `1 ≤ a < b`,
`Σ_{j≥b} π(j)φj(a, b)²/q(a, b) = O(Λ π(a)π(b)/(Π(a, b]Π[a, b]))`." Here, for the pair of
Algorithm 1, "`q(0, a) = π(a)`, `q(a, b) = π(a)κ(a, b) + π(b)κ(b, a) = 2Γ(a, b)`" (p.9).

There is an absolute constant `C > 0` such that, under the floor of Sec. 3.1, for every active rank `a`
the anchor load is at most `C π(a)/Π[1, a]`, and for all active ranks `a < b` the interval load is at
most `C Λ π(a)π(b)/(Π(a, b]Π[a, b])`.

**Formalization Note.** `O(·)` is one absolute constant, quantified before `m`, `ξ`, `π`; the target
sums run over the active ranks `j ≤ m`. -/
theorem lemma_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (ξ : ℝ) (π : ℕ → ℝ), IsFloored m ξ π →
      (∀ a ∈ Icc 1 m,
        (∑ j ∈ Icc a m, π j * phi π j 0 a ^ 2) / π a ≤ C * (π a / massCC π 1 a)) ∧
      (∀ a b : ℕ, 1 ≤ a → a < b → b ≤ m →
        (∑ j ∈ Icc b m, π j * phi π j a b ^ 2) / (2 * gamma m ξ π a b) ≤
          C * bigLambda m ξ * (π a * π b / (massOC π a b * massCC π a b))) := by sorry

end OrderedExperts
