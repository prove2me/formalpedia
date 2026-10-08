-- Prove2me | Theorems.Thm_GeometryOfGraphs_Clique_proposition_5_4
-- name    : GeometryOfGraphs.Clique.proposition_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:10:18.109228+00:00
-- url     : https://prove2.me/theorems/b20b25e4-94d1-4001-9033-37e56c8cc5fc
-- title:
--   Proposition 5.4 — isometric dimension of the complete graph
-- statement:
--   Let $K_n$ be the complete graph on $n\ge1$ vertices, with shortest-path distance. Its **isometric dimension**, minimized over all real norms, is
--
--   $$
--   \dim(K_n)=\lceil\log_2 n\rceil.
--   $$
--
--   Thus the dimension of a real normed space that realizes every edge of $K_n$ with length one grows exactly as the base-two logarithm of its number of vertices.
--
--   **Formalization Note** Lean uses `Nat.clog 2 n` for the ceiling, including its value zero at $n=1$. The graph distance is cast from a natural number to a real number. The paper assumes connected graphs; $n\ge1$ makes that convention explicit.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 231, Proposition 5.4

import Definitions.Def_GeometryOfGraphs_Clique_isoDim

namespace GeometryOfGraphs.Clique

/-- Proposition 5.4, p. 231: the isometric dimension of the complete graph. -/
theorem proposition_5_4 (n : ℕ) (hn : 0 < n) :
    isoDim (fun i j : Fin n => ((⊤ : SimpleGraph (Fin n)).dist i j : ℝ)) =
      Nat.clog 2 n := by sorry

end GeometryOfGraphs.Clique
