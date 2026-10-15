-- Prove2me | Theorems.Thm_LinExchangeSP_Revealed_corollary_4_1
-- name    : LinExchangeSP.Revealed.corollary_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:24.582077+00:00
-- url     : https://prove2.me/theorems/30aa5e47-a084-43f8-9717-a2d6556c7cf9
-- title:
--   Corollary 4.1, p. 8 — if F ⊆ F*, every F-equilibrium is supported on F*
-- statement:
--   Consider a linear exchange market and let $F^*$ be the set of edges that are maximum bang-per-buck edges in every market equilibrium. If $F\subseteq F^*$ and $(p,f)$ is an $F$-equilibrium (an $F$-allocation with $\lVert s(p,f)\rVert_1=0$), then
--   $$\operatorname{supp}(f)\subseteq F^*.$$
--
--   In the proof of Lemma 3.4 this places every edge used by an $F$-equilibrium among the MBB edges of every market equilibrium.
--
--   **Formalization Note** The paper writes "for every $F$-equilibrium $f$"; the prices $p$ of the $F$-equilibrium $(p,f)$ are explicit here.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 8, Corollary 4.1

import Mathlib
import Definitions.Def_LinExchangeSP_Revealed_Market
import Definitions.Def_LinExchangeSP_Revealed_Setting

namespace LinExchangeSP.Revealed
theorem corollary_4_1 {n : ℕ} (M : Market n) (F : Set (Fin n × Fin n)) (hF : F ⊆ M.Fstar)
    (p : Fin n → ℝ) (f : Fin n → Fin n → ℝ) (hpf : M.IsFEquilibrium F p f) :
    supp f ⊆ M.Fstar := by sorry
end LinExchangeSP.Revealed
