-- Prove2me | Theorems.Thm_NicerEars_TJoin_proposition_3
-- name    : NicerEars.TJoin.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:49.62977+00:00
-- url     : https://prove2.me/theorems/35c63b4e-bdad-432e-84ce-20d14903118e
-- title:
--   Proposition 3 — OPT(G,T) ≥ LP(G,T) ≥ |V(G)| − 1
-- statement:
--   Let $G$ be a connected graph and $T\subseteq V(G)$ with $|T|$ even. Then
--   $$\mathrm{OPT}(G,T)\ \ge\ \mathrm{LP}(G,T)\ \ge\ |V(G)|-1,$$
--   where $\mathrm{OPT}(G,T)$ is the minimum cardinality of a connected-$T$-join of $G$ and $\mathrm{LP}(G,T)$ is the LP relaxation of p. 5.
--
--   The first inequality says that $\mathrm{LP}(G,T)$ is a valid lower bound for the connected-$T$-join problem; the second is the lower bound used in the case of few pendant ears in the proof of Theorem 25.
--
--   **Formalization Note.** $\mathrm{OPT}(G,T)\ge \mathrm{LP}(G,T)$ is stated as: for every connected-$T$-join $F$ there is an $\mathrm{LP}(G,T)$-feasible $x$ with $x(E(G))\le|F|$. $\mathrm{LP}(G,T)\ge|V(G)|-1$ is stated as: every feasible $x$ has $x(E(G))\ge|V(G)|-1$. Both are equivalent to the inequalities between the minima.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 5, Proposition 3

import Mathlib
import Definitions.Def_NicerEars_TJoin_Setting

namespace NicerEars.TJoin

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Proposition 3 (Sebő–Vygen, arXiv:1201.1870v3, p. 5): for every connected graph `G` and
`T ⊆ V(G)` with `|T|` even, `OPT(G, T) ≥ LP(G, T) ≥ |V(G)| − 1`. The first inequality is stated as
"every connected-T-join `F` admits an LP(G, T)-feasible point of value at most `|F|`", the second as
"every LP(G, T)-feasible point has value at least `|V(G)| − 1`". -/
theorem proposition_3 (G : Graph V E) (hG : G.IsConnected) (T : Finset V) (hT : Even #T) :
    (∀ F : Finset (E × Fin 2), G.IsConnectedTJoin T F →
      ∃ x : E → ℝ, G.LPTFeasible T x ∧ ∑ e, x e ≤ (#F : ℝ)) ∧
    (∀ x : E → ℝ, G.LPTFeasible T x → (Fintype.card V : ℝ) - 1 ≤ ∑ e, x e) := by sorry

end NicerEars.TJoin
