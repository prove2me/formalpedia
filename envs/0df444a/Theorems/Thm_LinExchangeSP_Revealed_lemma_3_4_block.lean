-- Prove2me | Theorems.Thm_LinExchangeSP_Revealed_lemma_3_4_block
-- name    : LinExchangeSP.Revealed.lemma_3_4_block
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:19.631879+00:00
-- url     : https://prove2.me/theorems/8c9d31e7-2cc3-4e97-9009-af9d3285566e
-- title:
--   Proof of Lemma 3.4, p. 9 — Σ_{i∈S} p′_i = Σ_{g_j∈T} p′_j and T = {g_j | j ∈ S}
-- statement:
--   Consider a linear exchange market in which agent $i$ owns good $g_i$. Let $F\subseteq F^*$, let $(p,f)$ be an $F$-equilibrium and let $(p',f')$ be a market equilibrium. With
--   $$\alpha=\max_{g_j\in G}\frac{p'_j}{p_j},\qquad T=\Big\{g_j\in G:\frac{p'_j}{p_j}=\alpha\Big\},\qquad S=\{i\in A:\exists g_j\in T,\ (i,g_j)\in\mathrm{MBB}(p')\},$$
--   we have
--   $$\sum_{i\in S}p'_i=\sum_{g_j\in T}p'_j\qquad\text{and}\qquad T=\{g_j\in G: j\in S\}.$$
--
--   So the goods brought to the market by the agents of $S$ are exactly the goods of maximal price ratio $T$. The proof of Lemma 3.4 uses this to show that the agents of $S$ can spend their whole budgets on $T$ at prices $p$.
--
--   **Formalization Note** Agents and goods share the index type `Fin n`, so $T=\{g_j: j\in S\}$ is the equality $T=S$ of index sets. The paper's normalisations $p'\ne p$ and $\sum_j p'_j=\sum_j p_j$ are not assumed.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 9, proof of Lemma 3.4, displays (4)–(5) and the paragraph after them

import Mathlib
import Definitions.Def_LinExchangeSP_Revealed_Market
import Definitions.Def_LinExchangeSP_Revealed_Setting

namespace LinExchangeSP.Revealed
theorem lemma_3_4_block {n : ℕ} (M : Market n) (F : Set (Fin n × Fin n))
    (hF : F ⊆ M.Fstar) (p : Fin n → ℝ) (f : Fin n → Fin n → ℝ) (hpf : M.IsFEquilibrium F p f)
    (p' : Fin n → ℝ) (f' : Fin n → Fin n → ℝ) (hp'f' : M.IsMarketEquilibrium p' f') :
    ∑ i ∈ M.topAgents p p', p' i = ∑ j ∈ topGoods p p', p' j ∧
      topGoods p p' = M.topAgents p p' := by sorry
end LinExchangeSP.Revealed
