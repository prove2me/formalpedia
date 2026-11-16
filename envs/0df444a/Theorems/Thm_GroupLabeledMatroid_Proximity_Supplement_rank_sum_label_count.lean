-- Prove2me | Theorems.Thm_GroupLabeledMatroid_Proximity_Supplement_rank_sum_label_count
-- name    : GroupLabeledMatroid.Proximity.Supplement.rank_sum_label_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:39:52.827752+00:00
-- url     : https://prove2.me/theorems/72c4d09f-e2a7-4bb8-ab9f-103a4067b4ba
-- title:
--   Theorem 4 — rank-sum lower bound on the labels of cheap bases
-- statement:
--   Let $M=(E,\mathcal I)$ be a matroid on a finite ground set $E$ with rank function $r$, let $G$ be an abelian group (possibly infinite), $\ell:E\to G$ a labeling and $c:E\to\mathbb R$ a cost function. For $X\subseteq E$ write $\ell(X)=\sum_{e\in X}\ell(e)$ and $c(X)=\sum_{e\in X}c(e)$, and for $\theta\in\mathbb R$ let
--   $$\ell_{\le\theta}(M)=\{\ell(D): D \text{ is a base of } M \text{ with } c(D)\le\theta\}.$$
--   Suppose $B$ is the unique min-cost $\ell(B)$-base of $M$: $B$ is a base, and every base $D$ with $\ell(D)=\ell(B)$ satisfies $c(B)\le c(D)$, with equality only for $D=B$. For $h\in G$ let
--   $$R_h=\{e\in E:\ \ell(e)=h \text{ and } c(e)\le \min_{b\in B}c(b)\}.$$
--   Then
--   $$|\ell_{\le c(B)}(M)|\ \ge\ \sum_{h\in G} r(R_h)-r(E)+1.$$
--
--   This is a weighted analogue, valid for every abelian group, of the Schrijver–Seymour bound for $\mathbb Z_p$: under the uniqueness assumption on $B$ it bounds from below the number of distinct labels of bases of cost at most $c(B)$ by the rank sum of the cost-filtered color classes. Taking $c\equiv 0$ gives the unweighted Corollary 13.
--
--   **Formalization Note** $M$ is a Mathlib matroid on a finite type with ground `M.E`; $r(E)$ is the rank of the ground. Only labels occurring on the ground have nonempty $R_h$, so the sum over $G$ is the finite sum over $\ell[E]$. The minimum over $B$ is written as "$c(e)\le c(x)$ for all $x\in B$", which for rank $0$ ($B=\emptyset$) gives $R_h=E_h$; every set has rank $0$ then, so the statement is the paper's under any reading of $\min\emptyset$. The comparison is in $\mathbb Z$, since the right-hand side can be negative.
--
--   Differences from the source:
--   - encoding: finite ground set E and subsets → Finset subsets of a finite ambient type with ground M.E and natural ranks cast to ℤ; reason: every finite matroid admits this representation; the inequality is compared in ℤ, so no truncation occurs
--   - encoding: sum over h ∈ G → sum over the labels occurring on the ground; reason: every other h has R_h = ∅ of rank 0, so the sums are equal, and the sum is finite even for infinite G
--   - encoding: c(e) ≤ min_{b∈B} c(b) → c(e) ≤ c(x) for every x ∈ B; reason: equivalent for nonempty B; for B = ∅ (rank 0) all ranks vanish, so both sides are unchanged
-- source:
--   Siyue Liu, Taihei Oki, Chao Xu, Proximity Theorem and FPT Algorithm for Minimum Group-labeled Matroid Bases, STOC 2027 submission #554 (October 2026), p. 3, Theorem 4 (restated p. 8, proof pp. 6–8); notation ℓ≤θ(M) p. 6

import Definitions.Def_GroupLabeledMatroid_Proximity_LabelModel

namespace GroupLabeledMatroid.Proximity.Supplement

open GroupLabeledMatroid.Proximity

theorem rank_sum_label_count {E G : Type*} [Fintype E] [DecidableEq E] [AddCommGroup G] [DecidableEq G]
    (M : Matroid E) (ℓ : E → G) (c : E → ℝ) (B : Finset E)
    (hB : IsUniqueLabelMinimum M ℓ c B) :
    ((labelsUnder M ℓ c (costSum c B)).card : ℤ) ≥
      (∑ h ∈ (ground M).image ℓ,
          (rankOn M ((colorClass M ℓ h).filter (fun e => ∀ x ∈ B, c e ≤ c x)) : ℤ)) -
        (rankOn M (ground M) : ℤ) + 1 := by sorry

end GroupLabeledMatroid.Proximity.Supplement
