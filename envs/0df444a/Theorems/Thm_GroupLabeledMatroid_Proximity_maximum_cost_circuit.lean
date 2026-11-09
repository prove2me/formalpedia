-- Prove2me | Theorems.Thm_GroupLabeledMatroid_Proximity_maximum_cost_circuit
-- name    : GroupLabeledMatroid.Proximity.maximum_cost_circuit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:58.309926+00:00
-- url     : https://prove2.me/theorems/216d071e-dc30-4b61-944b-9f43a770d3b2
-- title:
--   Lemma 14 — maximum-cost circuit element
-- statement:
--   Let $M$ have positive rank and ground $E=A\mathbin{\dot\cup}B$, where $A$ is a minimum-cost base and $B$ is the unique minimum-cost base in its label fiber. Costs are arbitrary reals, labels lie in an arbitrary abelian group, and equal element costs are allowed. Every circuit $C$ has at least one maximum-cost element belonging to $B$:
--
--   $$\operatorname*{arg\,max}_{e\in C}c(e)\cap B\ne\varnothing.$$
--
--   The arg max contains all maximizers, so the assertion preserves ties. This constrains the circuit structure in the block setting.
--
--   Differences from the source:
--   - encoding: finite ground set E and finite subsets → Finset subsets of a finite ambient type with classical decidable equality, genuine Mathlib ground M.E, and finite natural ranks; reason: every finite source ground admits this representation; arbitrary subsets M.E support minors; finite rank conversion has no infinite case; classical equality imposes no restriction on the label group
--   - encoding: nonempty intersection with the set of all circuit maximizers → an element e in C∩B with c(f)≤c(e) for every f∈C; reason: exactly the same tied arg-max condition, with no chosen maximizer function
-- source:
--   Siyue Liu, Taihei Oki, Chao Xu, Proximity Theorem and FPT Algorithm for Minimum Group-labeled Matroid Bases, STOC 2027 submission #554 (October 2026), p. 8, Lemma 14; §3 p. 6 and §3.2 p. 8 standing hypotheses

import Definitions.Def_GroupLabeledMatroid_Proximity_ContractionFiltration
open scoped Pointwise

namespace GroupLabeledMatroid.Proximity

theorem maximum_cost_circuit {E G : Type*} [Fintype E] [DecidableEq E] [AddCommGroup G] [DecidableEq G]
    (M : Matroid E) (ℓ : E → G) (c : E → ℝ) (A B : Finset E)
    (hblock : IsBlockPair M ℓ c A B) (hpos : 0 < M.eRank.toNat)
    (C : Finset E) (hC : M.IsCircuit (C : Set E)) :
    ∃ e ∈ C ∩ B, ∀ f ∈ C, c f ≤ c e := by sorry

end GroupLabeledMatroid.Proximity
