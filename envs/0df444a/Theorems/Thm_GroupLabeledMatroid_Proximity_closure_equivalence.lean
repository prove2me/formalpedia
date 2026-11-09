-- Prove2me | Theorems.Thm_GroupLabeledMatroid_Proximity_closure_equivalence
-- name    : GroupLabeledMatroid.Proximity.closure_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:50.684206+00:00
-- url     : https://prove2.me/theorems/12b53287-3348-4b44-be46-35ad82cd2251
-- title:
--   Lemma 16 — cost-filtered closure equivalence
-- statement:
--   Let $M$ have positive rank and ground $E=A\mathbin{\dot\cup}B$, where $A$ is a minimum-cost base and $B$ is the unique minimum-cost base in its label fiber. Costs are arbitrary reals, labels lie in an arbitrary abelian group, and equal element costs are allowed. Order $B$ by nondecreasing cost and use the contractions and color sets of §3.1. For every $i\in[r]$ and $h\in G$,
--
--   $$b_i\in\operatorname{cl}_{M_i}(E_h^i)\quad\Longleftrightarrow\quad b_i\in\operatorname{cl}_{M_i}(R_h^i).$$
--
--   Both directions are included. This identifies when the cost filter preserves spanning of the pivot.
--
--   Differences from the source:
--   - encoding: finite ground set E and finite subsets → Finset subsets of a finite ambient type with classical decidable equality, genuine Mathlib ground M.E, and finite natural ranks; reason: every finite source ground admits this representation; arbitrary subsets M.E support minors; finite rank conversion has no infinite case; classical equality imposes no restriction on the label group
--   - encoding: indices i=1,…,r and terminal stage r+1 → i : Fin r represents source i+1; natural stage k represents source k+1; H is filtered over occurring ground labels; reason: prefix k contracts the first k base elements, stage r is terminal, and a nonloop pivot cannot be spanned by an empty color class, so filtering H changes no member
-- source:
--   Siyue Liu, Taihei Oki, Chao Xu, Proximity Theorem and FPT Algorithm for Minimum Group-labeled Matroid Bases, STOC 2027 submission #554 (October 2026), p. 9, Lemma 16; standing hypotheses and definitions pp. 6–8

import Definitions.Def_GroupLabeledMatroid_Proximity_ContractionFiltration
open scoped Pointwise

namespace GroupLabeledMatroid.Proximity

theorem closure_equivalence {E G : Type*} [Fintype E] [DecidableEq E] [AddCommGroup G] [DecidableEq G]
    (M : Matroid E) (ℓ : E → G) (c : E → ℝ) (A B : Finset E)
    (hblock : IsBlockPair M ℓ c A B) {r : ℕ} (hr : 0 < r)
    (b : Fin r → E) (horder : IsCostOrder c B b) (i : Fin r) (h : G) :
    b i ∈ (stageMinor M b i.val).closure (stageColor M ℓ b i.val h : Set E) ↔
      b i ∈ (stageMinor M b i.val).closure (stageR M ℓ c b i.val h : Set E) := by sorry

end GroupLabeledMatroid.Proximity
