-- Prove2me | Theorems.Thm_OPG37364_exists_high_girth_adjacency_expander
-- name    : OPG37364.exists_high_girth_adjacency_expander
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T10:47:54.4175+00:00
-- url     : https://prove2.me/theorems/14f84d0e-b540-407b-a1fe-aa0032257ee8
-- title:
--   High-girth bipartite fourteen-regular graphs with adjacency eigenvalues below twelve
-- statement:
--   For every integer $g\ge3$, there exist $n\ge2$ and a connected bipartite $14$-regular simple graph $G$ on $n$ vertices, of girth at least $g$, such that every real eigenvalue $\mu$ of its real adjacency matrix $A_G$ satisfies
--
--   $$\mu\ne14\quad\Longrightarrow\quad\mu<12.$$
--
--   The spectral condition uses Mathlib's real matrix spectrum directly and is one-sided; $-14$ is allowed. This is a weaker sufficient adjacency-spectrum specification implied by the stronger LPS bound, not a verbatim statement of the LPS Ramanujan theorem.
--
--   This is the remaining hard graph-existence input. No construction or spectral proof is supplied. The conclusion includes no Markov spectral gap, strict cut expansion, immunity or perfect matching.
-- source:
--   A weaker sufficient consequence of the LPS route used in Feghali--Lucke--Paulusma--Ries, Algorithmica 87 (2025), Lemma 5, https://link.springer.com/article/10.1007/s00453-025-01318-8. Lubotzky--Phillips--Sarnak, Ramanujan graphs, Combinatorica 8 (1988), abstract (i), https://link.springer.com/article/10.1007/BF02126799, bounds adjacency eigenvalues by ±k or absolute value at most 2 sqrt(k-1). For k=14 and eigenvalue different from 14, either it is -14 or it is at most 2 sqrt(13) < 12. The graph construction, connectedness, prescribed girth and spectral bound remain Open.

import Definitions.Def_opg37364_matching_cuts
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Analysis.Matrix.Spectrum

set_option autoImplicit false
open scoped Classical

namespace OPG37364

theorem exists_high_girth_adjacency_expander :
    ∀ g : ℕ, 3 ≤ g →
      ∃ n : ℕ, 2 ≤ n ∧ ∃ G : SimpleGraph (Fin n),
        IsConnected G ∧ IsBipartite G ∧ IsRegularOfDegree G 14 ∧
        HasGirthAtLeast G g ∧
        (∀ μ : ℝ, μ ∈ spectrum ℝ (G.adjMatrix ℝ) → μ ≠ 14 → μ < 12) := by sorry

end OPG37364
