-- Prove2me | Theorems.Thm_OrderedExperts_lemma_9
-- name    : OrderedExperts.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:35:32.620799+00:00
-- url     : https://prove2.me/theorems/c6907f55-a060-4ac6-ae1f-5f561bdabdf8
-- title:
--   Lemma 9 — coordinatewise self-bound
-- statement:
--   Let $\pi$ satisfy the floor $\pi(j)\ge\xi/m$ on the active ranks $1,\dots,m$ ($0<\xi\le1$, $\sum_j\pi(j)=1$), let $\Lambda=1+\log(m/\xi)$, and let $g$ be a hidden vector with $g(x_0)=0$. For every realization $(A,B)$ of the queried pair and every active rank $j$, the endpoint flow estimate satisfies
--   $$
--   \pi(j)\,|\hat g(j)|\le 3\Lambda\max_{0\le a<b\le m}|g(x_b)-g(x_a)|.
--   $$
--   In particular, $\pi(j)|\hat g(j)|\le3\Lambda$ when $g$ takes values in $[0,1]$.
--
--   This pathwise bound plays the role of the boundedness condition in the robust mirror-descent analysis.
--
--   Differences from the source:
--   - encoding: $\max_{0\le a<b\le m}|g(x_b)-g(x_a)|$ → any $M$ bounding all these increments; reason: taking $M$ equal to the maximum recovers the source; the two forms are equivalent
--   - encoding: every realization → every pair $(A,B)$ of active ranks; reason: under the floor every such pair has positive probability
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Lemma 9, p.19; Appendix A.6, p.19

import Definitions.Def_OrderedExperts_est
import Definitions.Def_OrderedExperts_IsFloored
open Finset

namespace OrderedExperts

/-- **Lemma 9 (Self-bound).** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Lemma 9, p.19: "For every realization and
every active rank `j`, `π(j)|ĝ(j)| ≤ 3Λ max_{0≤a<b≤m} |g(xb) − g(xa)|`, where `g(x0) = 0`. In
particular, the right side is at most `3Λ` when `g` takes values in `[0, 1]`."

Under the floor of Sec. 3.1, for every hidden vector `g` with `g(x0) = 0`, every bound `M` on the
increments `|g b − g a|` (`0 ≤ a < b ≤ m`), every realization `(A, B)` of the pair and every active
rank `j`, the endpoint-flow estimate satisfies `π(j)|ĝ(j)| ≤ 3ΛM`; and if `g` takes values in `[0, 1]`
on the active ranks, `π(j)|ĝ(j)| ≤ 3Λ`.

**Formalization Note.** A bound `M` valid for all pairs is equivalent to the maximum. Every pair of
active ranks is a realization (it has positive probability under the floor). -/
theorem lemma_9 (m : ℕ) (ξ : ℝ) (π : ℕ → ℝ) (hπ : IsFloored m ξ π) (g : ℕ → ℝ) (hg0 : g 0 = 0) :
    (∀ M : ℝ, (∀ a b : ℕ, a < b → b ≤ m → |g b - g a| ≤ M) →
      ∀ A ∈ Icc 1 m, ∀ B ∈ Icc 1 m, ∀ j ∈ Icc 1 m,
        π j * |est m ξ π g A B j| ≤ 3 * bigLambda m ξ * M) ∧
    ((∀ j ∈ Icc 1 m, 0 ≤ g j ∧ g j ≤ 1) →
      ∀ A ∈ Icc 1 m, ∀ B ∈ Icc 1 m, ∀ j ∈ Icc 1 m,
        π j * |est m ξ π g A B j| ≤ 3 * bigLambda m ξ) := by sorry

end OrderedExperts
