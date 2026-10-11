-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_5_path_refinement
-- name    : OneTwoThree.Weighting.lemma_5_path_refinement
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-11T08:43:08.333055+00:00
-- url     : https://prove2.me/theorems/d6776149-ae19-44e2-95f8-b7665a7474ce
-- title:
--   Lemma 5 path-control refinement: T-join weight reassignment with (iv)-(vi) distinguished-edge constraints
-- statement:
--   Keusch's Lemma 5 (arXiv:2303.02611v4, p. 6) builds its weighting in two stages: a parity subgraph (T-join) $E_o$ in a spanning tree -- $E_o$-odd incidence exactly on $V_o = R' \cup \{v \in B : \alpha(v) \neq 2\deg(v)\}$ -- then a per-vertex weight reassignment on the $E_o(v)$ edges by the three $\alpha$-cases ($\alpha(v) = 2\deg(v)-1$, $2\deg(v)$, $2\deg(v)+1$). No flow machinery is used; the s-t network belongs to Lemma 4. The path version's extra clauses (iv)-(vi) are a refinement of that same reassignment step: the 1/3 distribution inside each $E_o(v)$ is pinned by distinguished-element subset choices (from $\mathrm{Finset.exists\_subset\_card\_eq}$) so that (iv) the first path edge avoids weight 1 when $\alpha(a) = 2\deg(a)+1$ and avoids weight 3 otherwise, (v) the two incident path-edge weights at every interior $B$ path vertex sum to 3, 4, or 5, and (vi) the same as (iv) at $b$. This node states that refinement as an interface: given the T-join $E_o$ with its parity property plus the path data, there is a weighting $\omega$ satisfying all six clauses (i)-(vi) of Lemma 5's path version. The full $\mathrm{lemma\_5\_path}$ follows from the parity-subgraph child plus this node.
-- source:
--   Keusch, arXiv:2303.02611v4, proof of Lemma 5, p. 6

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

namespace OneTwoThree.Weighting

/-- Lemma 5 path-control refinement (Keusch, arXiv:2303.02611v4, proof of Lemma 5, p. 6).

The proof of Lemma 5 builds its weighting in two stages: a parity subgraph (T-join)
`E_o` in a spanning tree -- `E_o`-odd incidence exactly on
`V_o = R' ∪ {v ∈ B // α v ≠ 2 * G.degree v}` -- then a per-vertex weight
reassignment on the `E_o(v)` edges by the three `α` cases. No flow machinery is
used (the s-t network belongs to Lemma 4). The path version's extra clauses
(iv)-(vi) are a refinement of that same reassignment step: the 1/3 distribution
inside each `E_o(v)` is pinned by distinguished-element subset choices (from
`Finset.exists_subset_card_eq`) so that the first/last path edges avoid weight 1
(resp. 3) according to the `α`-endpoint case, and the two incident path-edge
weights at every interior `B` path vertex sum to 3, 4, or 5. This node states
that refinement as an interface: given the T-join `E_o` with its parity property
plus the path data, there is a weighting satisfying all six clauses (i)-(vi).
The full `lemma_5_path` follows from the parity-subgraph child plus this node. -/
theorem lemma_5_path_refinement {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (B : Finset V)
    (hB : ∀ u v, G.Adj u v → (u ∈ B ↔ v ∉ B)) (α : V → ℕ)
    (hα : ∀ v ∈ B, (α v : ℤ) = 2 * (G.degree v : ℤ) - 1 ∨ (α v : ℤ) = 2 * (G.degree v : ℤ) ∨
      (α v : ℤ) = 2 * (G.degree v : ℤ) + 1)
    (R' : Finset V) (hR' : R' ⊆ Bᶜ) (hpar : Even (Finset.card R' + Finset.sum B (fun v => α v)))
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hk : 2 ≤ p.length) (ha : a ∈ B) (hb : b ∈ B)
    (E_o : Finset (Sym2 V)) (hEsub : (E_o : Set (Sym2 V)) ⊆ G.edgeSet)
    (hEpar : ∀ v, Odd (Finset.card (E_o.filter (fun e => v ∈ e))) ↔
      v ∈ R' ∪ B.filter (fun u => α u ≠ 2 * G.degree u)) :
    ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧
      (∀ v ∈ Bᶜ \ R', Even (wdeg G ω v)) ∧
      (∀ v ∈ R', Odd (wdeg G ω v)) ∧
      (∀ v ∈ B, wdeg G ω v = α v) ∧
      -- (iv)
      (α a = 2 * G.degree a + 1 → ω s(p.getVert 0, p.getVert 1) ≠ 1) ∧
      (α a ≠ 2 * G.degree a + 1 → ω s(p.getVert 0, p.getVert 1) ≠ 3) ∧
      -- (v)
      (∀ j, 0 < j → j < p.length → p.getVert j ∈ B →
        ω s(p.getVert (j - 1), p.getVert j) + ω s(p.getVert j, p.getVert (j + 1)) ∈
          ({3, 4, 5} : Finset ℕ)) ∧
      -- (vi)
      (α b = 2 * G.degree b + 1 → ω s(p.getVert (p.length - 1), p.getVert p.length) ≠ 1) ∧
      (α b ≠ 2 * G.degree b + 1 → ω s(p.getVert (p.length - 1), p.getVert p.length) ≠ 3) := by sorry

end OneTwoThree.Weighting
