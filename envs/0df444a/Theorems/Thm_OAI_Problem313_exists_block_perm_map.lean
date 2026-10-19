-- Prove2me | Theorems.Thm_OAI_Problem313_exists_block_perm_map
-- name    : OAI.Problem313.exists_block_perm_map
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:01:33.897179+00:00
-- url     : https://prove2.me/theorems/273ad263-d730-44f1-bad7-ff9f056865bb
-- title:
--   Block permutations move any subset to any equal-size subset
-- statement:
--   Let $\alpha$ be finite, $B\subseteq\alpha$, and $s,t\subseteq B$ with $|s|=|t|$. Then there is a permutation $\pi$ of $\alpha$ fixing every point outside $B$ with
--   $$
--   \pi(s)=t .
--   $$
--
--   The symmetric group of the block acts transitively on its subsets of each size. Extending by the identity keeps the exterior fixed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockOrbits.lean#L11-L42

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits

open OAI OAI.Problem313
universe u

theorem OAI.Problem313.exists_block_perm_map {α : Type u} [Fintype α] [DecidableEq α]
    (B s t : Finset α) (hs : s ⊆ B) (ht : t ⊆ B)
    (hc : s.card = t.card) :
    ∃ π : Equiv.Perm α, (∀ u, u ∉ B → π u = u) ∧
      s.map π.toEmbedding = t := by sorry
