-- Prove2me | Theorems.Thm_GroupLabeledMatroid_Proximity_label_extension
-- name    : GroupLabeledMatroid.Proximity.label_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:54.363412+00:00
-- url     : https://prove2.me/theorems/cf0d3c5d-fe14-4f71-8fb5-be92f0414cd1
-- title:
--   Lemma 9 — cost-filtered label extension
-- statement:
--   Let $M$ be a finite matroid, $G$ an arbitrary abelian group, and $\ell$ and $c$ its label and real cost maps. Let $B$ be the unique minimum-cost base in its own label fiber, of positive rank $r$, ordered by nondecreasing cost. Use the source's contractions $M_i$, suffixes $B_{\ge i}$, and filtered sets $S_i,H_i$ from §§3–3.1. For every $i\in[r]$, $s\in S_{i+1}$ and $h\in H_i$, there exist a base $A$ of $M_{i+1}$ with $\ell(A)=s$ and an element $e$ with $\ell(e)=h$ such that
--
--   $$A'=A\cup\{e\}\text{ is a base of }M_i,\qquad c(A')\le c(B_{\ge i}).$$
--
--   In particular $S_{i+1}+H_i\subseteq S_i$. This is the extension step relating consecutive threshold label sets.
--
--   Differences from the source:
--   - encoding: finite ground set E and finite subsets → Finset subsets of a finite ambient type with classical decidable equality, genuine Mathlib ground M.E, and finite natural ranks; reason: every finite source ground admits this representation; arbitrary subsets M.E support minors; finite rank conversion has no infinite case; classical equality imposes no restriction on the label group
--   - encoding: indices i=1,…,r and terminal stage r+1 → i : Fin r represents source i+1; natural stage k represents source k+1; H is filtered over occurring ground labels; reason: prefix k contracts the first k base elements, stage r is terminal, and a nonloop pivot cannot be spanned by an empty color class, so filtering H changes no member
-- source:
--   Siyue Liu, Taihei Oki, Chao Xu, Proximity Theorem and FPT Algorithm for Minimum Group-labeled Matroid Bases, STOC 2027 submission #554 (October 2026), p. 7, Lemma 9; standing hypotheses and definitions pp. 6–7

import Definitions.Def_GroupLabeledMatroid_Proximity_ContractionFiltration
open scoped Pointwise

namespace GroupLabeledMatroid.Proximity

theorem label_extension {E G : Type*} [Fintype E] [DecidableEq E] [AddCommGroup G] [DecidableEq G]
    (M : Matroid E) (ℓ : E → G) (c : E → ℝ) (B : Finset E)
    (hB : IsUniqueLabelMinimum M ℓ c B) {r : ℕ} (hr : 0 < r)
    (b : Fin r → E) (horder : IsCostOrder c B b) (i : Fin r) :
    (∀ s ∈ stageS M ℓ c B b (i.val + 1), ∀ h ∈ stageH M ℓ c b i,
      ∃ (A : Finset E) (e : E),
        (stageMinor M b (i.val + 1)).IsBase (A : Set E) ∧ labelSum ℓ A = s ∧
        ℓ e = h ∧ (stageMinor M b i.val).IsBase ((insert e A : Finset E) : Set E) ∧
        costSum c (insert e A) ≤ costSum c (suffix B b i.val)) ∧
    stageS M ℓ c B b (i.val + 1) + stageH M ℓ c b i ⊆ stageS M ℓ c B b i.val := by sorry

end GroupLabeledMatroid.Proximity
