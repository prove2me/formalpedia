-- Prove2me | Theorems.Thm_ImplicitParityWL_Supplement_theorem_1_4
-- name    : ImplicitParityWL.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:29:22.176575+00:00
-- url     : https://prove2.me/theorems/f877829c-db6b-4ee4-a3e8-2a3f79f8b58a
-- title:
--   Theorem 1.4 — homomorphism witnesses of treewidth $\le k$ need $2^{\Omega_k(n^{k-1})}$ vertices
-- statement:
--   Let $k\ge3$ be fixed. There is a constant $c_k>0$ such that for every $n_0\in\mathbb N$ there are some $n\ge n_0$ and $n$-vertex colored graphs $G_0,G_1$, distinguished by $k$-WL, such that every colored graph $F$ with
--   $$\mathrm{tw}(F)\le k\quad\text{and}\quad\hom(F,G_0)\ne\hom(F,G_1)$$
--   satisfies
--   $$|V(F)|\ge2^{c_k\,n^{k-1}}.$$
--
--   By Dvořák's theorem such witnesses $F$ exist; the theorem says they are exponentially large in $n^{k-1}$, which is tight up to a logarithmic factor in the exponent (Theorem 10.11 with the stabilization bound of Döring and Neuen).
--
--   **Formalization Note** $G_0,G_1$ are colored graphs on $\{0,\dots,n-1\}$ over a common color set, "distinguished by $k$-WL" means that their round-$r$ histograms differ for some $r$, $F$ ranges over colored graphs over the same colors on every finite vertex set, and $\hom$ counts color-preserving homomorphisms. $\mathrm{tw}(F)\le k$ is the published `RobersonCx.TwLE`.
--
--   Differences from the source:
--   - reading: n-vertex graphs G0, G1 and colored graphs F → G0, G1 colored over an existential color type K, F colored over K; reason: F is colored and hom counts preserve colors; the proof uses the colored compiled graphs
--   - encoding: |V(F)| ≥ 2^(Ω_k(n^(k−1))) → ∃ c > 0 chosen before n₀ with 2^(c·n^(k−1)) ≤ |V(F)| (real exponent); reason: the constant of Ω_k depends on k alone
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Theorem 1.4, p.4 (restated p.59)

import Mathlib
import Definitions.Def_ImplicitParityWL_WLColor
import Definitions.Def_ImplicitParityWL_Supplement_Homomorphism

namespace ImplicitParityWL

namespace Supplement

/-- **Theorem 1.4** (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman
Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.4, restated p.59): let `k ≥ 3`
be fixed. For every `n₀ ∈ ℕ` there is some `n ≥ n₀` and `n`-vertex graphs `G₀`, `G₁`, distinguished by
`k`-WL, such that every colored graph `F` with `tw(F) ≤ k` and `hom(F, G₀) ≠ hom(F, G₁)` satisfies
`|V(F)| ≥ 2^{Ω_k(n^{k-1})}`.

**Formalization Note** The constant `c > 0` of `Ω_k` depends on `k` alone: it is chosen before `n₀`.
`G₀`, `G₁` are colored graphs on `Fin n` over a common color type `K`; "distinguished by `k`-WL" is
`DistinguishesAfter` at some round. `F` ranges over colored graphs over `K` on every finite vertex type,
`tw(F) ≤ k` is the published `RobersonCx.TwLE`, and `hom` counts color-preserving homomorphisms. -/
theorem theorem_1_4 (k : ℕ) (hk : 3 ≤ k) : ∃ c : ℝ, 0 < c ∧ ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧
    ∃ (K : Type) (G₀ G₁ : ColoredGraph K (Fin n)), (∃ r : ℕ, DistinguishesAfter G₀ G₁ k r) ∧
      ∀ (U : Type) [Fintype U] (F : ColoredGraph K U), RobersonCx.TwLE F.graph k →
        homCount F G₀ ≠ homCount F G₁ →
          (2 : ℝ) ^ (c * (n : ℝ) ^ (k - 1)) ≤ (Fintype.card U : ℝ) := by sorry

end Supplement

end ImplicitParityWL
