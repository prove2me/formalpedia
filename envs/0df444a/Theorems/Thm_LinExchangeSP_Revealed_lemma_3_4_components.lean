-- Prove2me | Theorems.Thm_LinExchangeSP_Revealed_lemma_3_4_components
-- name    : LinExchangeSP.Revealed.lemma_3_4_components
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:22.907666+00:00
-- url     : https://prove2.me/theorems/cd9a35b6-8391-4785-9c15-ebe478163a9a
-- title:
--   Proof of Lemma 3.4, p. 9 — S ∪ T is a union of connected components of (A ∪ G, F ∪ supp(f))
-- statement:
--   Consider a linear exchange market. Let $F\subseteq F^*$, let $(p,f)$ be an $F$-equilibrium and let $(p',f')$ be a market equilibrium. Put $\bar E=F\cup\operatorname{supp}(f)$,
--   $$\alpha=\max_{g_j\in G}\frac{p'_j}{p_j},\qquad T=\Big\{g_j\in G:\frac{p'_j}{p_j}=\alpha\Big\},\qquad S=\{i\in A:\exists g_j\in T,\ (i,g_j)\in\mathrm{MBB}(p')\}.$$
--   Then $S\cup T$ is a union of connected components of the undirected bipartite graph $(A\cup G,\bar E)$: whenever two vertices lie in the same connected component, either both belong to $S\cup T$ or neither does.
--
--   This is the structural step of the proof of Lemma 3.4: the agents of $S$ and the goods of $T$ form a block of $\bar E$ that can be removed before repeating the argument.
--
--   **Formalization Note** The vertices of the graph are agents `inl i` and goods `inr j`; "belongs to $S\cup T$" means $i\in S$ for an agent and $j\in T$ for a good. The paper's normalisations $p'\ne p$ and $\sum_j p'_j=\sum_j p_j$ are not needed for this claim and are not assumed.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 9, proof of Lemma 3.4, third paragraph

import Mathlib
import Definitions.Def_LinExchangeSP_Revealed_Market
import Definitions.Def_LinExchangeSP_Revealed_Setting

namespace LinExchangeSP.Revealed
theorem lemma_3_4_components {n : ℕ} (M : Market n) (F : Set (Fin n × Fin n))
    (hF : F ⊆ M.Fstar) (p : Fin n → ℝ) (f : Fin n → Fin n → ℝ) (hpf : M.IsFEquilibrium F p f)
    (p' : Fin n → ℝ) (f' : Fin n → Fin n → ℝ) (hp'f' : M.IsMarketEquilibrium p' f')
    (a b : Fin n ⊕ Fin n) (hab : (bipGraph (F ∪ supp f)).Reachable a b) :
    (M.inBlock p p' a ↔ M.inBlock p p' b) := by sorry
end LinExchangeSP.Revealed
