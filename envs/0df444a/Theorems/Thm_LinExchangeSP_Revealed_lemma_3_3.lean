-- Prove2me | Theorems.Thm_LinExchangeSP_Revealed_lemma_3_3
-- name    : LinExchangeSP.Revealed.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:11.76614+00:00
-- url     : https://prove2.me/theorems/8e5e529a-db04-4588-9d18-18a0afc0f0d7
-- title:
--   Lemma 3.3, p. 6 — in an F-allocation with F ⊆ F*, an edge carrying more than ‖s(p, f)‖₁ is revealed
-- statement:
--   Consider a linear exchange market with edge set $E$, and let $F^*$ be the set of edges that are maximum bang-per-buck edges in every market equilibrium. Let $F\subseteq F^*$ and let $(p,f)$ be an $F$-allocation, so that money may be negative on edges of $F$ but nonnegative elsewhere, every money-carrying edge and every edge of $F$ is MBB at $p$, and no agent overspends and no good is oversold. If an edge $(k,g_\ell)\in E$ carries
--   $$f_{k\ell}>\lVert s(p,f)\rVert_1,$$
--   then $(k,g_\ell)\in F^*$.
--
--   This is the step by which the algorithm of the paper enlarges its revealed edge set $F$: an edge carrying more money than the total surplus must be MBB in every equilibrium.
--
--   **Formalization Note** No hypothesis that a market equilibrium exists is needed: if none exists, $F^*=E$ and the conclusion is the hypothesis $(k,g_\ell)\in E$. The inequality is strict, as in the paper.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 6, Lemma 3.3 (proof on p. 8)

import Mathlib
import Definitions.Def_LinExchangeSP_Revealed_Market
import Definitions.Def_LinExchangeSP_Revealed_Setting

namespace LinExchangeSP.Revealed
theorem lemma_3_3 {n : ℕ} (M : Market n) (F : Set (Fin n × Fin n)) (hF : F ⊆ M.Fstar)
    (p : Fin n → ℝ) (f : Fin n → Fin n → ℝ) (hpf : M.IsFAllocation F p f)
    (k l : Fin n) (hk : (k, l) ∈ M.E) (hbig : surplusL1 p f < f k l) :
    (k, l) ∈ M.Fstar := by sorry
end LinExchangeSP.Revealed
