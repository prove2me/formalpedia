-- Prove2me | Theorems.Thm_NicerEars_TJoin_theorem_25
-- name    : NicerEars.TJoin.theorem_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:03.016205+00:00
-- url     : https://prove2.me/theorems/48b5660b-6499-45a4-8a18-a84625668d14
-- title:
--   Theorem 25 — every connected graph has a connected-T-join with at most 3/2 LP(G,T) edges
-- statement:
--   For any connected graph $G$ and $T\subseteq V(G)$ with $|T|$ even, there is a connected-$T$-join $F$ of $G$ (a $T$-join in $2G$ whose edges connect $V(G)$) with
--   $$|F|\ \le\ \tfrac32\,\mathrm{LP}(G,T).$$
--   Since $\mathrm{LP}(G,T)\le\mathrm{OPT}(G,T)$, this is a $\tfrac32$-approximation guarantee for the connected-$T$-join problem, which contains graphic $s$-$t$-path TSP ($|T|=2$); it also shows that the integrality ratio of $\mathrm{LP}(G,T)$ is at most $\tfrac32$.
--
--   **Formalization Note.** The paper states an algorithm running in $O(|V(G)|^3)$ time; the algorithm and its running time are not formalized, only the existence of the connected-$T$-join for every input. "$|F|\le\tfrac32\mathrm{LP}(G,T)$" is stated as $|F|\le\tfrac32\,x(E(G))$ for every feasible point $x$ of $\mathrm{LP}(G,T)$, with $F$ chosen before $x$; this is equivalent to the bound on the minimum. Graphs may have parallel edges, and $F$ may use each edge at most twice.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 19, Theorem 25

import Mathlib
import Definitions.Def_NicerEars_TJoin_Setting

namespace NicerEars.TJoin

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Theorem 25 (p. 19), existence part: for any connected graph `G` and `T ⊆ V(G)` with `|T|` even
there is a connected-T-join `F` of `G` with `|F| ≤ 3/2 LP(G, T)`, i.e. `|F| ≤ 3/2 · x(E(G))` for
every feasible point `x` of LP(G, T). -/
theorem theorem_25 (G : Graph V E) (hG : G.IsConnected) (T : Finset V) (hT : Even #T) :
    ∃ F : Finset (E × Fin 2), G.IsConnectedTJoin T F ∧
      ∀ x : E → ℝ, G.LPTFeasible T x → (#F : ℝ) ≤ 3 / 2 * ∑ e, x e := by sorry

end NicerEars.TJoin
