-- Prove2me | Theorems.Thm_OPG37364_spectralGap_gt_one_seventh_of_adjacency_bound
-- name    : OPG37364.spectralGap_gt_one_seventh_of_adjacency_bound
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T10:46:08.007072+00:00
-- url     : https://prove2.me/theorems/76cafb36-8916-4319-8a81-45e96251c311
-- title:
--   Adjacency eigenvalues below twelve give ordinary walk gap above one seventh
-- statement:
--   Let $G$ be a connected finite $14$-regular simple graph, and let $A$ be its real adjacency matrix. Suppose every real eigenvalue $\mu$ of $A$ whose value is not $14$ satisfies $\mu<12$.
--
--   Then the ordinary simple-random-walk matrix $P_G$ satisfies
--
--   $$\operatorname{spectralGap}(P_G)>\frac17.$$
--
--   The matrix is $P_G=A/14$. The platform definition of the ordinary gap is $1-\sup\{r: r\text{ is a real eigenvalue of }P_G,\ r\ne1\}$. The adjacency hypothesis is expressed directly by Mathlib real matrix spectrum membership, with a strict one-sided bound. It permits the bipartite eigenvalue $-14$ and does not use the absolute spectral gap. No bipartiteness, girth, cut expansion, immunity or perfect-matching assumption is required.
--
--   **Formalization Note.** The direct value-based formulation avoids identifying an ordered second eigenvalue with a value-excluding supremum. Connectedness is an explicit hypothesis; no simplicity theorem for the top eigenvalue is an additional assumption.
-- source:
--   Standard finite-dimensional matrix scaling and finite-spectrum argument, using Mathlib matrix spectrum and the exact MarkovMixing definitions. This supplies a sufficient normalization step for the proof route in Feghali--Lucke--Paulusma--Ries, Algorithmica 87 (2025), Lemma 5, https://link.springer.com/article/10.1007/s00453-025-01318-8. The threshold 12 is weaker than the LPS bound 2 sqrt(13); this theorem is not a graph-existence or LPS theorem.

import Definitions.Def_opg37364_matching_cuts
import Definitions.Def_mm_spectral
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Analysis.Matrix.Spectrum

set_option autoImplicit false
open scoped Classical

namespace OPG37364

theorem spectralGap_gt_one_seventh_of_adjacency_bound
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hconn : IsConnected G) (hreg : IsRegularOfDegree G 14)
    (hAdj : ∀ μ : ℝ, μ ∈ spectrum ℝ (G.adjMatrix ℝ) → μ ≠ 14 → μ < 12) :
    (1 : ℝ) / 7 < MarkovMixing.spectralGap (MarkovMixing.graphWalk G) := by sorry

end OPG37364
