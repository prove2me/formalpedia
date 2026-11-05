-- Prove2me | Theorems.Thm_NicerEars_TJoin_theorem_25_twoVertexConnected
-- name    : NicerEars.TJoin.theorem_25_twoVertexConnected
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T11:24:54.271752+00:00
-- url     : https://prove2.me/theorems/f1c9a657-c409-449f-bda0-6e0a4cf86e7d
-- title:
--   Theorem 25 for 2-vertex-connected graphs: a connected-T-join with at most 3/2 LP(G,T) edges
-- statement:
--   Let $G$ be a 2-vertex-connected graph (parallel edges allowed) and $T\subseteq V(G)$ with $|T|$ even. Then there is a connected-$T$-join $F$ of $G$ (a $T$-join in $2G$ whose edges connect $V(G)$) with
--   $$|F|\ \le\ \tfrac32\,x(E(G))$$
--   for every feasible point $x$ of $\mathrm{LP}(G,T)$, i.e. $|F|\le\frac32\,\mathrm{LP}(G,T)$.
--
--   This is the case of Theorem 25 to which its proof reduces at the outset ('We may assume that $G$ is 2-vertex-connected (Proposition 4)'); the rest of the proof of Theorem 25 (Lemma 23, Theorem 24, Theorem 20, Propositions 3 and 8) is exactly a proof of this statement.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 19, Theorem 25 and its proof (the 2-vertex-connected case)

import Mathlib
import Definitions.Def_NicerEars_TJoin_Setting

namespace NicerEars.TJoin

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Theorem 25 (p. 19) in the 2-vertex-connected case ("We may assume that G is 2-vertex-connected
(Proposition 4)"): for a 2-vertex-connected graph `G` and `T ⊆ V(G)` with `|T|` even there is a
connected-T-join `F` with `|F| ≤ 3/2 · x(E(G))` for every feasible point `x` of LP(G, T). -/
theorem theorem_25_twoVertexConnected (G : Graph V E) (hG : G.IsTwoVertexConnected) (T : Finset V)
    (hT : Even #T) :
    ∃ F : Finset (E × Fin 2), G.IsConnectedTJoin T F ∧
      ∀ x : E → ℝ, G.LPTFeasible T x → (#F : ℝ) ≤ 3 / 2 * ∑ e, x e := by sorry

end NicerEars.TJoin
