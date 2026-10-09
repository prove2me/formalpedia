-- Prove2me | Theorems.Thm_NicerEars_TJoin_proposition_6
-- name    : NicerEars.TJoin.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:46.218372+00:00
-- url     : https://prove2.me/theorems/ec0662e8-48f2-4627-8434-897bec6185bb
-- title:
--   Proposition 6 (Frank) — τ(G,T) ≤ ½(|V(G)| + ϕ(G) − 1)
-- statement:
--   (Frank 1993.) Let $G$ be a 2-edge-connected graph and $T\subseteq V(G)$ with $|T|$ even. Then the minimum cardinality $\tau(G,T)$ of a $T$-join in $G$ satisfies
--   $$\tau(G,T)\ \le\ \tfrac12\bigl(|V(G)|+\varphi(G)-1\bigr),$$
--   where $\varphi(G)$ is the minimum number of even ears in an ear-decomposition of $G$.
--
--   This bounds the parity-correction step in the proof of Theorem 24.
--
--   **Formalization Note.** $\tau(G,T)\le b$ is stated as the existence of a $T$-join $F\subseteq E(G)$ (each edge at most once) with $|F|\le b$.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 7, Proposition 6 (Frank [1993])

import Mathlib
import Definitions.Def_NicerEars_TJoin_Ears

namespace NicerEars.TJoin

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Proposition 6 (Frank [1993]; p. 7): for a 2-edge-connected graph `G` and `T ⊆ V(G)` with `|T|`
even, `τ(G, T) ≤ ½(|V(G)| + ϕ(G) − 1)`, stated as the existence of a T-join `F ⊆ E(G)` of that
size. -/
theorem proposition_6 (G : Graph V E) (hG : G.IsTwoEdgeConnected) (T : Finset V) (hT : Even #T) :
    ∃ F : Finset E, G.IsTJoin T F ∧
      (#F : ℝ) ≤ 1 / 2 * ((Fintype.card V : ℝ) + phi G - 1) := by sorry

end NicerEars.TJoin
