-- Prove2me | Theorems.Thm_OPG37364_smallCut_expansion_of_spectralGap_gt_one_seventh
-- name    : OPG37364.smallCut_expansion_of_spectralGap_gt_one_seventh
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T09:50:36.287168+00:00
-- url     : https://prove2.me/theorems/12e70db9-6139-430b-85a3-d2d119da75f1
-- title:
--   Ordinary random-walk gap above one seventh forces strict small-cut expansion
-- statement:
--   Let $G$ be a connected $14$-regular finite simple graph on $n\ge2$ vertices. Let $P$ be its ordinary simple-random-walk transition matrix, with entry $1/14$ on an adjacency and zero otherwise. Write $\gamma(P)=1-\lambda_2(P)$ for the ordinary spectral gap, where $\lambda_2$ is the largest real eigenvalue different from one.
--
--   If $\gamma(P)>1/7$, then every nonempty proper shore $S$ satisfying $|S|\le|V\setminus S|$ has strictly more crossing pairs than vertices:
--
--   $$|S|<|\operatorname{cutPairs}(G,S)|.$$
--
--   Each crossing edge is counted once, from $S$ into its complement. The spectral inequality and the expansion conclusion are both strict. The theorem requires neither bipartiteness nor a girth bound, and uses the ordinary gap rather than the absolute gap.
-- source:
--   A regular-graph consequence of Levin--Peres--Wilmer, Markov Chains and Mixing Times, Theorem 13.14 (upper Cheeger bound), as formalized by MarkovMixing.cheeger_upper, Prove2Me ID 8e914dfd-cd15-4c4b-b173-c4c80670bd47, accepted solution https://prove2.me/api/v1/submissions/eff72ab6-82ba-426f-a096-60e18752c4dc/solution . Applied to the expansion route in Feghali--Lucke--Paulusma--Ries, Algorithmica 87 (2025), Lemma 5, https://link.springer.com/article/10.1007/s00453-025-01318-8

import Definitions.Def_opg37364_cut_pairs
import Definitions.Def_mm_spectral

set_option autoImplicit false
open scoped Classical

namespace OPG37364

theorem smallCut_expansion_of_spectralGap_gt_one_seventh
    {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (hconn : IsConnected G) (hreg : IsRegularOfDegree G 14)
    (hgap : (1 : ℝ) / 7 < MarkovMixing.spectralGap (MarkovMixing.graphWalk G)) :
    ∀ S : Set (Fin n), S.Nonempty → Sᶜ.Nonempty →
      S.encard ≤ Sᶜ.encard → S.encard < (cutPairs G S).encard := by sorry

end OPG37364
