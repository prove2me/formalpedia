-- Prove2me | Theorems.Thm_OSPMech_SqrtLB_theorem_3
-- name    : OSPMech.SqrtLB.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:53.494854+00:00
-- url     : https://prove2.me/theorems/820aebc5-a0a9-4a3d-8895-5ebb87cb3e8b
-- title:
--   Theorem 3, p. 8 — OSP CMON: a tree admits OSP payments iff no OSP-graph has a negative-weight cycle
-- statement:
--   Let $\mathcal T$ be an implementation tree for $n$ agents with finite type domains $D_i$, outcomes in a set $\mathcal S$, and costs $a(X)$ for an agent of type $a$ and outcome $X$. For each agent $i$, let $\mathcal O_i^{\mathcal T}$ be the OSP-graph: its nodes are the profiles of $D$, and there is an edge from $\mathbf a = (a, \mathbf a_{-i})$ to $\mathbf b = (b, \mathbf b_{-i})$ whenever both are compatible with a vertex labelled $i$ at which they diverge, with weight $a(f(\mathbf b)) - a(f(\mathbf a))$.
--
--   Then there is a payment function $\mathbf p$ making $(\mathcal T, \mathbf p)$ obviously strategyproof if and only if, for every agent $i$,
--   $$\mathcal O_i^{\mathcal T} \text{ has no cycle of negative total weight.}$$
--
--   This is the extension of Rochet's cycle monotonicity from direct mechanisms to extensive-form mechanisms ("OSP CMON"). Its "only if" direction applied to cycles of length two gives the monotonicity constraints used in the lower bound of Theorem 12.
--
--   **Formalization Note.** "Is an OSP mechanism for $f$" is read as "some payment function makes it OSP", as in the proof (p. 24). The edge weight is that of the proof (p. 24) and of Observation 1; Definition 2 prints the opponents' profiles swapped. A cycle is a closed walk $\mathbf w_0 \to \mathbf w_1 \to \dots \to \mathbf w_k \to \mathbf w_0$ along edges.
-- source:
--   Ferraioli, Meier, Penna, Ventre, On the approximation guarantee of obviously strategyproof mechanisms, arXiv:1805.04190v2, p. 8, Definition 2 and Theorem 3; proof p. 24 (App. A.1)

import Mathlib
import Definitions.Def_OSPMech_SqrtLB_Model

namespace OSPMech.SqrtLB
theorem theorem_3 {n : ℕ} {X : Type} (D : Fin n → Finset ℝ) (cost : Fin n → ℝ → X → ℝ)
    (t : ImplTree n X) :
    (∃ p : (Fin n → ℝ) → Fin n → ℝ, IsOSP D cost t p) ↔ ∀ i, NoNegCycle D cost t i := by sorry
end OSPMech.SqrtLB
