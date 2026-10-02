-- Prove2me | Theorems.Thm_OPG37364_exists_high_girth_spectral_expander
-- name    : OPG37364.exists_high_girth_spectral_expander
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T09:51:10.65269+00:00
-- url     : https://prove2.me/theorems/1b251773-0536-424f-98fc-88f9451c2250
-- title:
--   High-girth bipartite fourteen-regular graphs with ordinary spectral gap above one seventh
-- statement:
--   For every integer $g\ge3$, there exist $n\ge2$ and a connected bipartite $14$-regular simple graph $G$ on $n$ vertices with girth at least $g$ such that its ordinary simple-random-walk spectral gap satisfies
--
--   $$\gamma(P_G)=1-\lambda_2(P_G)>\frac17.$$
--
--   Here $P_G(x,y)=1/14$ on adjacent pairs and zero otherwise, and $\lambda_2$ is the largest real eigenvalue different from one. This is an ordinary spectral-gap existence assertion; the negative eigenvalue of a bipartite walk is allowed. Its conclusion contains neither cut expansion, immunity, nor a perfect matching.
--
--   This remains the hard graph-construction and spectral input in the LPS route. No proof of the LPS construction, its girth, or its spectral bound is supplied by this statement.
-- source:
--   Feghali--Lucke--Paulusma--Ries, Algorithmica 87 (2025), proof of Lemma 5, https://link.springer.com/article/10.1007/s00453-025-01318-8. The construction cited there has adjacency second eigenvalue at most 2 sqrt(13). For a connected 14-regular graph, the ordinary walk matrix is A/14, so the corresponding expected bound is gamma >= 1 - sqrt(13)/7 > 1/7. Establishing the graph construction and its spectral identification remains Open; the normalization from the cited LPS adjacency operator is not assumed as a proved helper.

import Definitions.Def_opg37364_matching_cuts
import Definitions.Def_mm_spectral

set_option autoImplicit false
open scoped Classical

namespace OPG37364

theorem exists_high_girth_spectral_expander :
    ∀ g : ℕ, 3 ≤ g →
      ∃ n : ℕ, 2 ≤ n ∧ ∃ G : SimpleGraph (Fin n),
        IsConnected G ∧ IsBipartite G ∧ IsRegularOfDegree G 14 ∧
        HasGirthAtLeast G g ∧
        (1 : ℝ) / 7 < MarkovMixing.spectralGap (MarkovMixing.graphWalk G) := by sorry

end OPG37364
