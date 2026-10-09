-- Prove2me | Theorems.Thm_NicerEars_TwoEC_theorem_7
-- name    : NicerEars.TwoEC.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:46.86242+00:00
-- url     : https://prove2.me/theorems/34dc1846-589c-4179-a389-a181080d9b3d
-- title:
--   Theorem 7 (Frank 1993) — some even T has τ(G,T) = ½(|V(G)| + ϕ(G) − 1)
-- statement:
--   Let $G$ be a 2-edge-connected graph. Then there is a set $T\subseteq V(G)$ with $|T|$ even such that the minimum size of a $T$-join of $G$ satisfies
--
--   $$\tau(G,T)=\tfrac12\bigl(|V(G)|+\varphi(G)-1\bigr),$$
--
--   where $\varphi(G)$ is the minimum number of even ears in an ear-decomposition of $G$. Moreover $G$ has an ear-decomposition with exactly $\varphi(G)$ even ears.
--
--   The theorem shows that the bound $\tau(G,T)\le\frac12(|V(G)|+\varphi(G)-1)$ (Proposition 6) is attained, and it is the input of the lower bound $L_\varphi(G)\le\mathrm{LP}(G)$ of Theorem 19.
--
--   **Formalization Note** The identity is stated as $2\tau(G,T)=|V(G)|+\varphi(G)-1$ in the integers. The algorithmic part of the theorem (finding $T$ and the ear-decomposition in $O(|V(G)||E(G)|)$ time) is replaced by the existence of these objects.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 8, Theorem 7 (Frank [1993])

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Ears

namespace NicerEars.TwoEC

open Finset

theorem theorem_7 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hG : G.IsTwoEdgeConnected) :
    (∃ T : Finset V, Even #T ∧ 2 * (G.tau T : ℤ) = Fintype.card V + G.phi - 1) ∧
      ∃ D : EarDecomposition G, D.numEven = G.phi := by sorry

end NicerEars.TwoEC
