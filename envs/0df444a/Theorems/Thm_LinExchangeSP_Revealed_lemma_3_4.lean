-- Prove2me | Theorems.Thm_LinExchangeSP_Revealed_lemma_3_4
-- name    : LinExchangeSP.Revealed.lemma_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:20.614322+00:00
-- url     : https://prove2.me/theorems/09dea6e3-b107-46ae-a8d5-5ea8e8459acc
-- title:
--   Lemma 3.4, p. 6 — if F ⊆ F* and (p, f) is an F-equilibrium, the prices p support a market equilibrium (p, f′)
-- statement:
--   Consider a linear exchange market that has at least one market equilibrium, and let $F^*$ be the set of edges that are maximum bang-per-buck edges in every market equilibrium. Let $F\subseteq F^*$ and let $(p,f)$ be an $F$-equilibrium: $p>0$, money is nonnegative off $F$ (it may be negative on $F$), every money-carrying edge and every edge of $F$ is MBB at $p$, no agent overspends, no good is oversold, and
--   $$\lVert s(p,f)\rVert_1=0.$$
--   Then there is a money flow $f'$ such that $(p,f')$ is a market equilibrium.
--
--   This is how the algorithm of the paper finishes: once it has an $F$-equilibrium for a set $F$ of revealed edges, the same prices carry a genuine equilibrium, with nonnegative money on MBB edges only.
--
--   **Formalization Note** The paper states that $(p,f')$ "can be obtained in $O(nm)$ time" by one maximum-flow computation; the running time is not formalized, and the existence of $f'$ is what is posed. The hypothesis that some market equilibrium exists is added. The paper's proof starts from a market equilibrium $(p',f')$; the paper guarantees one through its standing assumption $(\star)$ that the digraph $(A,\bar E)$ with $(i,j)\in\bar E$ iff $u_{ij}>0$ is strongly connected, together with Gale's existence criterion (Lemma 2.3, cited). Assuming existence directly makes the statement more general than under $(\star)$ and does not require Gale's theorem. Without it the statement is false: if no equilibrium exists, $F^*=E$, and there are markets with an $E$-equilibrium but no market equilibrium.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 6, Lemma 3.4 (proof on p. 9; standing assumption (⋆) and Lemma 2.3 on p. 5)

import Mathlib
import Definitions.Def_LinExchangeSP_Revealed_Market
import Definitions.Def_LinExchangeSP_Revealed_Setting

namespace LinExchangeSP.Revealed
theorem lemma_3_4 {n : ℕ} (M : Market n) (F : Set (Fin n × Fin n)) (hF : F ⊆ M.Fstar)
    (hex : ∃ p' f', M.IsMarketEquilibrium p' f')
    (p : Fin n → ℝ) (f : Fin n → Fin n → ℝ) (hpf : M.IsFEquilibrium F p f) :
    ∃ f' : Fin n → Fin n → ℝ, M.IsMarketEquilibrium p f' := by sorry
end LinExchangeSP.Revealed
