-- Prove2me | Theorems.Thm_GeometryOfGraphs_Clique_cube_upper_bound
-- name    : GeometryOfGraphs.Clique.cube_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:09:46.339993+00:00
-- url     : https://prove2.me/theorems/4ef096d5-e0c4-4481-aa21-1fda70f037bc
-- title:
--   Proposition 5.4 proof — isometric embedding into a binary cube
-- statement:
--   For every positive integer $n$, the complete graph $K_n$ with its shortest-path metric embeds isometrically into $\ell_\infty^{\lceil\log_2 n\rceil}$:
--
--   $$
--   K_n\hookrightarrow\ell_\infty^{\lceil\log_2 n\rceil}.
--   $$
--
--   The cube realization gives the upper bound in Proposition 5.4.
--
--   **Formalization Note** The norm on the function space is the supremum norm. The intended map chooses distinct binary cube vertices. The shortest-path distance on $K_n$ is zero on the diagonal and one between distinct vertices.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 231, proof of Proposition 5.4, last paragraph

import Definitions.Def_GeometryOfGraphs_Clique_isoDim

namespace GeometryOfGraphs.Clique

/-- The cube embedding in the last paragraph of Proposition 5.4, p. 231. -/
theorem cube_upper_bound (n : ℕ) (hn : 0 < n) :
    ∃ φ : Fin n → (Fin (Nat.clog 2 n) → ℝ),
      ∀ i j, ‖φ i - φ j‖ = ((⊤ : SimpleGraph (Fin n)).dist i j : ℝ) := by sorry

end GeometryOfGraphs.Clique
