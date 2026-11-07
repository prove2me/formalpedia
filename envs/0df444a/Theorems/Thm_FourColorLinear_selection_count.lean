-- Prove2me | Theorems.Thm_FourColorLinear_selection_count
-- name    : FourColorLinear.selection_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:55.951421+00:00
-- url     : https://prove2.me/theorems/f8903fba-3300-4f6e-85ae-4a70fd40b219
-- title:
--   Selecting $Z^\prime$: strictly contained configurations, $\Omega(n)$ of them, completions inside a leaf
-- statement:
--   For a division $(R_i)$ of a plane triangulation and a pairwise non-touching induced family $Z$, let $Z'$ be the members strictly contained in a region, $Z\subseteq R_i-\partial R_i$. Then
--   $$|Z|\le|Z'|+\sum_i|\partial R_i|,$$
--   and each member of $Z'$ has its whole free completion in its region. Moreover, for all constants $c,K_r,K_b,\lambda,H$, there are $n_0$ and $c'>0$ such that if $n\ge n_0$, the division is an $r$-division with these constants, $\lambda\log_2 n\le r\le n$, and $|Z|\ge cn$, then $|Z'|\ge c'n$.
--
--   This is the selection of the subfamily in Task 5; with $Z'\subseteq$ leaves of size $\Theta(\log n)$, table look-ups handle a ring without touching the rest of the graph.
--
--   Differences from the source:
--   - generalization: the leaf regions of the recursive r⃗-division, r = ℓ = Θ(log n) → any division in the first clauses; any r with λ log₂ n ≤ r ≤ n in the last; reason: the counts use only these; the printed r is in the range
--   - reading: "we still have Ω(n)" → for n ≥ n₀ with c′ after the constants; reason: O(n/√log n) is below cn only for large n; for smaller n, Task 5 takes Z′ = Z
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), §2.1, p.14

import Mathlib
import Definitions.Def_FourColorLinear_Occurrence
import Definitions.Def_FourColorLinear_IsRegion

open PlanarQueue.Genus

namespace FourColorLinear

open Classical in
/-- The selection of `Z′`, arXiv:2610.39753 (held version, sha256 4dce39c5…), p.14: "Z′ = {Z ∈ Z | Z is strictly contained in some leaf region R,
that is, Z ⊆ R − ∂R}. The total number of boundary vertices of leaf regions is O(n/√log n). Since our
Ω(n) reducible configurations are non-touching and each has only a constant number of vertices, we
still have Ω(n) reducible configurations for which no vertex is a boundary vertex of a leaf region.
These are the reducible configurations Z in Z′. If Z is in the region R, then its ring vertices may
intersect ∂R, but its completion Ẑ, that is Z completed with its ring, is still contained in R."

**Formalization Note** The first two clauses hold for any division. The third is the `Ω(n)`, at an
`r`-division with `r ≥ λ log₂ n`. For `n < n₀` no bound is claimed. -/
theorem selection_count :
    (∀ {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (S : EmbeddingScheme G)
      (_ : IsPlaneTriangulation S) {k : ℕ} (Rs : Fin k → Set (Sym2 (Fin n))) (_ : IsDivision S Rs)
      {𝒟 : List Config} (Zs : List (OccIn S 𝒟)) (_ : IsNonTouchingFamily Zs),
      (Zs.length ≤ (Zs.countP fun z => decide (∃ i, z.2.verts ⊆ edgeVerts (Rs i) \ boundaryVerts S (Rs i))) +
          ∑ i, (boundaryVerts S (Rs i)).ncard) ∧
      ∀ z ∈ Zs, ∀ i, z.2.verts ⊆ edgeVerts (Rs i) \ boundaryVerts S (Rs i) →
        ∀ d : (𝒟[z.1]).G.Dart, s(z.2.hom d.fst, z.2.hom d.snd) ∈ Rs i) ∧
    ∀ (c Kr Kb lam : ℝ) (H : ℕ), 0 < c → 0 < lam →
      ∃ (n₀ : ℕ) (c' : ℝ), 0 < c' ∧
        ∀ {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (S : EmbeddingScheme G)
          (_ : IsPlaneTriangulation S) {k : ℕ} (Rs : Fin k → Set (Sym2 (Fin n))) (r : ℕ),
          n₀ ≤ n → lam * Real.logb 2 n ≤ r → r ≤ n → IsRDivision S Rs r Kr Kb H →
          ∀ {𝒟 : List Config} (Zs : List (OccIn S 𝒟)), IsNonTouchingFamily Zs → c * n ≤ Zs.length →
            c' * n ≤ (Zs.countP fun z =>
              decide (∃ i, z.2.verts ⊆ edgeVerts (Rs i) \ boundaryVerts S (Rs i)) : ℕ) := by sorry

end FourColorLinear
