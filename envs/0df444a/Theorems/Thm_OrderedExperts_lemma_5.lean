-- Prove2me | Theorems.Thm_OrderedExperts_lemma_5
-- name    : OrderedExperts.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:33:48.757933+00:00
-- url     : https://prove2.me/theorems/9b198fe0-2ebc-4d4a-8566-669fb3967830
-- title:
--   Lemma 5 — ordered cut bound
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $\pi$ satisfy the floor $\pi(j)\ge\xi/m$ on the active ranks $1,\dots,m$ ($0<\xi\le1$, $\sum_j\pi(j)=1$) and let $\Lambda=1+\log(m/\xi)$. Let $g$ be any real vector on the chain, extended by $g(x_0)=0$, with increments $H(a,b)=g(x_b)-g(x_a)$, and let
--   $$
--   V=|g(x_1)|+\sum_{j=2}^m|g(x_j)-g(x_{j-1})|
--   $$
--   be its total variation on the chain extended by the anchor. Then
--   $$
--   \sum_{a=1}^m H(0,a)^2\frac{\pi(a)}{\Pi[1,a]}+\sum_{1\le a<b\le m}H(a,b)^2\frac{\pi(a)\pi(b)}{\Pi(a,b]\,\Pi[a,b]}\le C\,\Lambda\,V^2.
--   $$
--
--   Combined with Lemmas 3 and 4 this gives the $O(\Lambda^2)$ second moment of Theorem 1, the variation of $g$ entering through $V$.
--
--   Differences from the source:
--   - encoding: $O(\Lambda V^2)$ → one absolute constant $C>0$ chosen before $m$, $\xi$, $\pi$, $g$; reason: meaning of $O(\cdot)$ in the paper
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Lemma 5, p.10; Appendix A.5, p.19

import Definitions.Def_OrderedExperts_massCC
import Definitions.Def_OrderedExperts_massOC
import Definitions.Def_OrderedExperts_bigLambda
import Definitions.Def_OrderedExperts_IsFloored
open Finset

namespace OrderedExperts

/-- **Lemma 5 (Ordered cut bound).** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Lemma 5, p.10: "Let
`H(a, b) = g(xb) − g(xa)` with `g(x0) = 0`, and let `V = |g(x1)| + TV(g)` be the total variation of `g`
on the chain extended by the anchor. Then `Σ_a H(0, a)² π(a)/Π[1, a] + Σ_{1≤a<b} H(a, b)²
π(a)π(b)/(Π(a, b]Π[a, b]) = O(ΛV²)`." `TV(g) = Σ_{j=2}^m |g(xj) − g(xj−1)|` (Sec. 2.1, p.5).

There is an absolute constant `C > 0` such that, under the floor of Sec. 3.1, for every real vector `g`
on the active chain the weighted sum of squared increments is at most `C Λ V²`.

**Formalization Note.** `g(x0) = 0` is built in (`H(0, a) = g a`); `g` is any real vector, with no
range or sign condition; `O(·)` is one absolute constant, quantified before `m`, `ξ`, `π`, `g`. -/
theorem lemma_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (ξ : ℝ) (π g : ℕ → ℝ), IsFloored m ξ π →
      ∑ a ∈ Icc 1 m, g a ^ 2 * (π a / massCC π 1 a) +
          ∑ a ∈ Icc 1 m, ∑ b ∈ Ioc a m,
            (g b - g a) ^ 2 * (π a * π b / (massOC π a b * massCC π a b)) ≤
        C * bigLambda m ξ * (|g 1| + ∑ j ∈ Icc 2 m, |g j - g (j - 1)|) ^ 2 := by sorry

end OrderedExperts
