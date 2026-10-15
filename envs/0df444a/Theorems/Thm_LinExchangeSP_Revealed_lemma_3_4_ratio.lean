-- Prove2me | Theorems.Thm_LinExchangeSP_Revealed_lemma_3_4_ratio
-- name    : LinExchangeSP.Revealed.lemma_3_4_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:16.24297+00:00
-- url     : https://prove2.me/theorems/1242789e-6d5b-48ca-956b-c42cd3099693
-- title:
--   Proof of Lemma 3.4, p. 9 — on a component of (A ∪ G, Ē) with Ē MBB at p and p′, p_j/p_k = p′_j/p′_k
-- statement:
--   Consider a linear exchange market, two positive price vectors $p,p'>0$, and a set of edges $\bar E\subseteq\mathrm{MBB}(p)\cap\mathrm{MBB}(p')$. If goods $g_j$ and $g_k$ lie in the same connected component of the undirected bipartite graph $(A\cup G,\bar E)$, then
--   $$\frac{p_j}{p_k}=\frac{p'_j}{p'_k}.$$
--
--   In the proof of Lemma 3.4 this is applied to $\bar E=F\cup\operatorname{supp}(f)$ for an $F$-equilibrium $(p,f)$ and a market equilibrium $(p',f')$: within one component the two price vectors are proportional.
--
--   **Formalization Note** The paper obtains $\bar E\subseteq\mathrm{MBB}(p)$ from Definition 3.2(ii) and $\bar E\subseteq\mathrm{MBB}(p')$ from Corollary 4.1; here both inclusions are hypotheses on an arbitrary edge set, which is all the claim uses.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 9, proof of Lemma 3.4, second and third paragraphs

import Mathlib
import Definitions.Def_LinExchangeSP_Revealed_Market
import Definitions.Def_LinExchangeSP_Revealed_Setting

namespace LinExchangeSP.Revealed
theorem lemma_3_4_ratio {n : ℕ} (M : Market n) (p p' : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hp' : ∀ j, 0 < p' j) (Ebar : Set (Fin n × Fin n))
    (h1 : Ebar ⊆ M.MBB p) (h2 : Ebar ⊆ M.MBB p') (j k : Fin n)
    (hjk : (bipGraph Ebar).Reachable (Sum.inr j) (Sum.inr k)) :
    p j / p k = p' j / p' k := by sorry
end LinExchangeSP.Revealed
