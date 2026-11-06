-- Prove2me | Theorems.Thm_OrderedExperts_lemma_7
-- name    : OrderedExperts.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:35:41.030035+00:00
-- url     : https://prove2.me/theorems/d817d177-0a26-4e50-b410-15071353919f
-- title:
--   Lemma 7 — edge-use probabilities of the random path
-- statement:
--   Let $\pi$ be positive on the active ranks $1,\dots,m$ and fix a target rank $j\in\{1,\dots,m\}$. Consider the random increasing path that starts at the anchor $0$ and, from a node $a<j$, jumps to $b\in\{a+1,\dots,j\}$ with probability $\pi(b)/\Pi(a,j]$. The probabilities $\varphi_j(a,b)$ that the path uses the anchor edge $(0,a)$ and the interval edge $(a,b)$ are
--   $$
--   \varphi_j(0,a)=\frac{\pi(a)}{\Pi[1,j]}\quad(1\le a\le j),\qquad
--   \varphi_j(a,b)=\frac{\pi(a)\pi(b)}{\Pi[a,j]\,\Pi(a,j]}\quad(1\le a<b\le j),
--   $$
--   and the edge-use probability is zero outside $0\le a<b\le j$.
--
--   This identifies the probabilistic flows with the closed forms used by the endpoint flow estimate, and so yields the flow identity $g(x_j)=\sum_e\varphi_j(e)H(e)$ for those closed forms.
--
--   Differences from the source:
--   - generalization: the standing floor of Section 3 ($\pi(j)\ge\xi/m$, $\pi$ a distribution) → $\pi(r)>0$ on the active ranks; reason: the floor implies positivity; the computation uses only positivity, so the statement specializes to the source
--   - encoding: probability that the random path traverses the edge → `pathFlow`, reach probability times next-step probability; reason: the path is strictly increasing, so it visits each node at most once and the two agree
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Lemma 7, p.18; Appendix A.3, p.18

import Definitions.Def_OrderedExperts_pathFlow
import Definitions.Def_OrderedExperts_massCC
open Finset

namespace OrderedExperts

/-- **Lemma 7 (Edge-use probabilities).** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Lemma 7, p.18: "The
probabilities that the path uses the anchor edge `(0, a)` and the interval edge `(a, b)` are
`φj(0, a) = π(a)/Π[1, j]` (`a ≤ j`), `φj(a, b) = π(a)π(b)/(Π[a, j]Π(a, j])` (`1 ≤ a < b ≤ j`). The
edge-use probability is zero outside `0 ≤ a < b ≤ j`." The path is that of Appendix A.3, p.18: "at
node `a < j` the path jumps to `b ∈ {a + 1, . . . , j}` with probability `π(b)/Π(a, j]`."

For `π` positive on the active ranks `1, …, m` and a target `j ∈ {1, …, m}`, the edge-use
probabilities `pathFlow π j` of the random increasing path are given by the closed forms above.

**Formalization Note.** Only positivity of `π` on the active ranks is assumed (the floor of Sec. 3.1
implies it). -/
theorem lemma_7 (m : ℕ) (π : ℕ → ℝ) (hπ : ∀ r ∈ Icc 1 m, 0 < π r) (j : ℕ) (hj : j ∈ Icc 1 m) :
    (∀ a ∈ Icc 1 j, pathFlow π j 0 a = π a / massCC π 1 j) ∧
    (∀ a b : ℕ, 1 ≤ a → a < b → b ≤ j →
      pathFlow π j a b = π a * π b / (massCC π a j * massOC π a j)) ∧
    (∀ a b : ℕ, ¬ (a < b ∧ b ≤ j) → pathFlow π j a b = 0) := by sorry

end OrderedExperts
