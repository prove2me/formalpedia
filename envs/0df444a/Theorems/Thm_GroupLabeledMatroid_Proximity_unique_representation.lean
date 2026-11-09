-- Prove2me | Theorems.Thm_GroupLabeledMatroid_Proximity_unique_representation
-- name    : GroupLabeledMatroid.Proximity.unique_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:52.843254+00:00
-- url     : https://prove2.me/theorems/09fdc727-06e4-45f2-8ceb-d6d9727aae17
-- title:
--   Lemma 10 — unique representation
-- statement:
--   Let $M$ be a finite matroid, $G$ an arbitrary abelian group, and $\ell$ and $c$ its label and real cost maps. Let $B$ be the unique minimum-cost base in its own label fiber, of positive rank $r$, ordered by nondecreasing cost. Use the source's contractions $M_i$, suffixes $B_{\ge i}$, and filtered sets $S_i,H_i$ from §§3–3.1. For every $i\in[r]$, the suffix label $g=\ell(B_{\ge i})$ has exactly one representation
--
--   $$g=s+h,\qquad s\in S_{i+1},\ h\in H_i.$$
--
--   Existence and uniqueness of the ordered pair are both asserted. This supplies the uniqueness condition for Kemperman–Scherk.
--
--   Differences from the source:
--   - encoding: finite ground set E and finite subsets → Finset subsets of a finite ambient type with classical decidable equality, genuine Mathlib ground M.E, and finite natural ranks; reason: every finite source ground admits this representation; arbitrary subsets M.E support minors; finite rank conversion has no infinite case; classical equality imposes no restriction on the label group
--   - encoding: indices i=1,…,r and terminal stage r+1 → i : Fin r represents source i+1; natural stage k represents source k+1; H is filtered over occurring ground labels; reason: prefix k contracts the first k base elements, stage r is terminal, and a nonloop pivot cannot be spanned by an empty color class, so filtering H changes no member
-- source:
--   Siyue Liu, Taihei Oki, Chao Xu, Proximity Theorem and FPT Algorithm for Minimum Group-labeled Matroid Bases, STOC 2027 submission #554 (October 2026), p. 7, Lemma 10; standing hypotheses and definitions pp. 6–7

import Definitions.Def_GroupLabeledMatroid_Proximity_ContractionFiltration
open scoped Pointwise

namespace GroupLabeledMatroid.Proximity

theorem unique_representation {E G : Type*} [Fintype E] [DecidableEq E] [AddCommGroup G] [DecidableEq G]
    (M : Matroid E) (ℓ : E → G) (c : E → ℝ) (B : Finset E)
    (hB : IsUniqueLabelMinimum M ℓ c B) {r : ℕ} (hr : 0 < r)
    (b : Fin r → E) (horder : IsCostOrder c B b) (i : Fin r) :
    ∃! p : G × G,
      p.1 ∈ stageS M ℓ c B b (i.val + 1) ∧ p.2 ∈ stageH M ℓ c b i ∧
      p.1 + p.2 = labelSum ℓ (suffix B b i.val) := by sorry

end GroupLabeledMatroid.Proximity
