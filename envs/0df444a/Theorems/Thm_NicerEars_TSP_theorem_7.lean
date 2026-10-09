-- Prove2me | Theorems.Thm_NicerEars_TSP_theorem_7
-- name    : NicerEars.TSP.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:08.462305+00:00
-- url     : https://prove2.me/theorems/d03574fd-d4cf-4cd4-81ab-1b0fedca50a2
-- title:
--   Theorem 7 (Frank) — some even T has τ(G, T) = ½(|V(G)| + ϕ(G) − 1)
-- statement:
--   **Theorem 7** (Frank [1993]). Let $G$ be a 2-edge-connected graph. Then there is a set $T\subseteq V(G)$ with $|T|$ even such that
--
--   $$\tau(G,T)=\tfrac12\big(|V(G)|+\varphi(G)-1\big),$$
--
--   where $\tau(G,T)$ is the minimum cardinality of a $T$-join in $G$ and $\varphi(G)$ is the minimum number of even ears in an ear-decomposition of $G$. Moreover $G$ has an ear-decomposition with exactly $\varphi(G)$ even ears.
--
--   Together with Proposition 6 ($\tau(G,T)\le\frac12(|V(G)|+\varphi(G)-1)$ for every even $T$) this identifies $\varphi(G)$ through $T$-joins; it is the source of the lower bound $L_\varphi(G)\le\mathrm{LP}(G)$ of Theorem 19.
--
--   **Formalization Note.** The equation is stated as $2\tau(G,T)=|V(G)|+\varphi(G)-1$ in the integers. The algorithmic part of the theorem (computing such a $T$ and decomposition in $O(|V(G)||E(G)|)$ time) is not formalized; only the existence of the decomposition is stated.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 8, Theorem 7 (Frank [1993])

import Mathlib
import Definitions.Def_NicerEars_TSP_Ears

namespace NicerEars.TSP

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Theorem 7 (Frank [1993]), p. 8: for a 2-edge-connected graph G there is T ⊆ V(G), |T| even,
with τ(G, T) = ½(|V(G)| + ϕ(G) − 1), and G has an ear-decomposition with ϕ(G) even ears. -/
theorem theorem_7 (G : Graph V E) (hG : G.IsTwoEdgeConnected) :
    (∃ T : Finset V, Even #T ∧ 2 * (G.tau T : ℤ) = Fintype.card V + G.phi - 1) ∧
    ∃ D : EarDecomposition G, D.numEven = G.phi := by sorry

end NicerEars.TSP
