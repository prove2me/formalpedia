-- Prove2me | Theorems.Thm_OAI_Problem313_Reindex_influence_le_total_div
-- name    : OAI.Problem313.Reindex.influence_le_total_div
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:58:30.019785+00:00
-- url     : https://prove2.me/theorems/01569fbe-5368-48ca-8f16-d0a464ec83fb
-- title:
--   Equal influences on many coordinates are small
-- statement:
--   Let $\iota$ be finite, $0\le p\le1$, $f:\{0,1\}^\iota\to\{0,1\}$, and let $I_j$ be the $p$-biased pivotal influence of coordinate $j$. If $S\subseteq\iota$ has at least $m>0$ elements and $I_j=I_i$ for all $j\in S$, then
--   $$
--   I_i\le\frac1m\sum_{j\in\iota}I_j .
--   $$
--
--   For a symmetric property, each influence is at most the total influence divided by the orbit size.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/InfluenceReindex.lean#L81-L102

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

open OAI OAI.Problem313 OAI.Problem313.Reindex
universe u v
variable {ι : Type u} {κ : Type v}

theorem OAI.Problem313.Reindex.influence_le_total_div [Fintype ι] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (ι → Bool) → Bool) (i : ι)
    (S : Finset ι) {m : ℝ} (hm : 0 < m) (hcard : m ≤ (S.card : ℝ))
    (heq : ∀ j ∈ S, influence p f j = influence p f i) :
    influence p f i ≤ (∑ j, influence p f j) / m := by sorry
