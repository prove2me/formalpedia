-- Prove2me | Theorems.Thm_ImpatientMatching_padding
-- name    : ImpatientMatching.padding
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:25.720242+00:00
-- url     : https://prove2.me/theorems/846152b1-2b95-4dd4-a1ed-e2769632b26c
-- title:
--   Padding by disjoint copies preserves the source promise
-- statement:
--   Let $H$ be a graph on $n$ vertices, $K$ a threshold and $r\ge1$. Replacing $H$ by $r$ disjoint copies and $K$ by $rK$ has the following properties.
--
--   1. The source range is preserved: if $H$ is cubic and $n/2\le K<n$, the same holds for the copies and $rK$.
--   2. If $\tau(H)\le K$, then the copies have $\tau\le rK$.
--   3. If $\tau(H)\ge(1+\varepsilon)K$, then the copies have $\tau\ge(1+\varepsilon)rK$.
--
--   Moreover, for $n\ge1$, $n_0\ge1$ and $r=\lceil n_0/n\rceil$, we have $r\ge 1$, $rn\ge n_0$ and $r\le n_0$.
--
--   This justifies the assumption $n\ge n_0$ throughout both reductions.
--
--   Differences from the source:
--   - reading: the instance size increases by at most a fixed factor → the number of vertices is multiplied by r ≤ n₀; reason: the vertex count determines the encoded size of the graph up to a square, which is the only use of the claim
--   - generalization: the cubic source graph H of (6) and the fixed n₀ of (9) or (37) → any finite simple graph for the cover clauses, and any n₀ ≥ 1 for the ceiling clauses; reason: the cubic graphs and both source values of n₀ are special cases
--   - encoding: ⌈n₀/n⌉ → the hypothesis 1 ≤ n; reason: excludes only n = 0, where n₀/n is undefined (a cubic graph has n ≥ 4)
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), §4.1, p.11, and (38), p.29

import Definitions.Def_ImpatientMatching_Source

open NSWApxHard.Reduction

namespace ImpatientMatching

/-- **Padding.** Yan–Varma, manuscript (sha256 7b1051b6…), §4.1, p.11, and (38), p.29: `r` disjoint copies of `H` with `K` scaled by `r`
preserve the source range and the two sides of the promise, and with `r = ⌈n₀/n⌉` the size reaches
`n₀` with a copying factor bounded by the fixed constant `n₀`.

**Formalization Note.** `SimpleGraph` makes the union simple by construction. -/
theorem padding :
    (∀ (H : GraphInput) (K r : ℕ), 1 ≤ r →
      (IsSourceRange H K → IsSourceRange (copies r H) (r * K)) ∧
      (tau H ≤ K → tau (copies r H) ≤ r * K) ∧
      ((1 + (eps : ℝ)) * (K : ℝ) ≤ (tau H : ℝ) →
        (1 + (eps : ℝ)) * ((r * K : ℕ) : ℝ) ≤ (tau (copies r H) : ℝ))) ∧
    (∀ (H : GraphInput) (n₀ : ℕ), 1 ≤ H.N → 1 ≤ n₀ →
      1 ≤ ⌈(n₀ : ℝ) / (H.N : ℝ)⌉₊ ∧
      n₀ ≤ (copies ⌈(n₀ : ℝ) / (H.N : ℝ)⌉₊ H).N ∧
      ⌈(n₀ : ℝ) / (H.N : ℝ)⌉₊ ≤ n₀) := by sorry

end ImpatientMatching
