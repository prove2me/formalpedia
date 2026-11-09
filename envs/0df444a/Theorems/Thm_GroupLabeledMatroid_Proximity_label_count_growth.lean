-- Prove2me | Theorems.Thm_GroupLabeledMatroid_Proximity_label_count_growth
-- name    : GroupLabeledMatroid.Proximity.label_count_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:01.586466+00:00
-- url     : https://prove2.me/theorems/f7e434c7-fc0f-4ff1-9527-2d858b04e23f
-- title:
--   Corollary 11 — label-count growth
-- statement:
--   Let $M$ be a finite matroid, $G$ an arbitrary abelian group, and $\ell$ and $c$ its label and real cost maps. Let $B$ be the unique minimum-cost base in its own label fiber, of positive rank $r$, ordered by nondecreasing cost. Use the source's contractions $M_i$, suffixes $B_{\ge i}$, and filtered sets $S_i,H_i$ from §§3–3.1. At every stage $i\in[r]$,
--
--   $$|S_i|\ge |S_{i+1}|+|H_i|-1.$$
--
--   This counts the growth of threshold labels before a contraction and retains the exact additive constant.
--
--   Differences from the source:
--   - encoding: finite ground set E and finite subsets → Finset subsets of a finite ambient type with classical decidable equality, genuine Mathlib ground M.E, and finite natural ranks; reason: every finite source ground admits this representation; arbitrary subsets M.E support minors; finite rank conversion has no infinite case; classical equality imposes no restriction on the label group
--   - encoding: indices i=1,…,r and terminal stage r+1 → i : Fin r represents source i+1; natural stage k represents source k+1; H is filtered over occurring ground labels; reason: prefix k contracts the first k base elements, stage r is terminal, and a nonloop pivot cannot be spanned by an empty color class, so filtering H changes no member
--   - encoding: integer cardinal difference |S_i| ≥ |S_{i+1}|+|H_i|−1 → |S_i|+1 ≥ |S_{i+1}|+|H_i| in natural numbers; reason: subtraction-free equivalent avoids truncated subtraction
-- source:
--   Siyue Liu, Taihei Oki, Chao Xu, Proximity Theorem and FPT Algorithm for Minimum Group-labeled Matroid Bases, STOC 2027 submission #554 (October 2026), p. 7, Corollary 11; standing hypotheses and definitions pp. 6–7

import Definitions.Def_GroupLabeledMatroid_Proximity_ContractionFiltration
open scoped Pointwise

namespace GroupLabeledMatroid.Proximity

theorem label_count_growth {E G : Type*} [Fintype E] [DecidableEq E] [AddCommGroup G] [DecidableEq G]
    (M : Matroid E) (ℓ : E → G) (c : E → ℝ) (B : Finset E)
    (hB : IsUniqueLabelMinimum M ℓ c B) {r : ℕ} (hr : 0 < r)
    (b : Fin r → E) (horder : IsCostOrder c B b) (i : Fin r) :
    (stageS M ℓ c B b i.val).card + 1 ≥
      (stageS M ℓ c B b (i.val + 1)).card + (stageH M ℓ c b i).card := by sorry

end GroupLabeledMatroid.Proximity
