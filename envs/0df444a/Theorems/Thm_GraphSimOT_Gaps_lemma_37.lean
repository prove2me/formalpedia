-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_lemma_37
-- name    : GraphSimOT.Gaps.lemma_37
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:07:37.01204+00:00
-- url     : https://prove2.me/theorems/55a3aed4-9d64-4778-89d9-f95182c9ab04
-- title:
--   Lemma 37 — local agreement for the cut distance: n⁻² Σ Q_ij |x_i − (Qᵀx)_j| ≤ 4ζ_Q for x = Ay, y ∈ [0,1]ⁿ
-- statement:
--   Let $G, H$ be graphs on $[n]$, $n\ge2$ (App. E.2), with adjacency matrices $A, B$, let $Q\in\mathrm{DS}(n)$, $y\in[0,1]^n$ and $x := Ay\in\mathbb R^n$. Then
--   $$\frac1{n^2}\sum_{i,j\in[n]}Q_{ij}\,\big|x_i - (Q^\top x)_j\big|\ \le\ 4\,\zeta_Q,$$
--   where $(Q^\top x)_j = \sum_iQ_{ij}x_i$ and $\zeta_Q = n^{-2}\|B(G,H,Q)\|_\square$ (Eq. (21)).
--
--   A fractional alignment of small cut cost only matches vertices with similar neighbourhood counts into every set $Y$; this is the second ingredient of Theorem 38.
--
--   Differences from the source:
--   - encoding: indices in [n] = {1, …, n} → Fin n = {0, …, n − 1}; reason: relabelling of the index set; no instance changes
--   - encoding: ζ_Q of the fixed graphs G, H of App. E.2 → zeta G H Q with G H : SimpleGraph (Fin n) as parameters; reason: the section fixes G, H; the statement holds for each pair
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 33, Lemma 37

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances
import Definitions.Def_GraphSimOT_Gaps_CutRounding

open Matrix

namespace GraphSimOT.Gaps

/-- Lemma 37 (Local Agreement, App. E.2, p. 33): for `Q ∈ DS(n)`, `y ∈ [0, 1]^n` and
`x := A y` (`A` the adjacency matrix of `G`),
`n^{-2} ∑_{i,j} Q_ij |x_i − (Qᵀ x)_j| ≤ 4 ζ_Q`. -/
theorem lemma_37 {n : ℕ} (hn : 2 ≤ n) (G H : SimpleGraph (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q ∈ doublyStochastic ℝ (Fin n))
    (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) :
    (1 / (n : ℝ) ^ 2) * ∑ i, ∑ j, Q i j * |(adj G *ᵥ y) i - (Qᵀ *ᵥ (adj G *ᵥ y)) j|
      ≤ 4 * zeta G H Q := by sorry

end GraphSimOT.Gaps
