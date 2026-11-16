-- Prove2me | Theorems.Thm_GroupLabeledMatroid_Proximity_Supplement_filtered_rank_drop
-- name    : GroupLabeledMatroid.Proximity.Supplement.filtered_rank_drop
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:39:30.188867+00:00
-- url     : https://prove2.me/theorems/2abc12eb-4dec-4d0e-87eb-96094597f2b4
-- title:
--   Lemma 12 — filtered color-rank drop under contraction of $b_i$
-- statement:
--   Let $M=(E,\mathcal I)$ be a matroid on a finite ground set $E$, $G$ an arbitrary abelian group, $\ell:E\to G$ a labeling and $c:E\to\mathbb R$ a cost function. For $X\subseteq E$ write $\ell(X)=\sum_{e\in X}\ell(e)$ and $c(X)=\sum_{e\in X}c(e)$. Suppose $B$ is the unique min-cost $\ell(B)$-base of $M$: $B$ is a base, and every base $D$ with $\ell(D)=\ell(B)$ satisfies $c(B)\le c(D)$, with equality only for $D=B$. Let $r\ge 1$ be the rank and enumerate $B=\{b_1,\dots,b_r\}$ with $c(b_1)\le\dots\le c(b_r)$.
--
--   For $i\in[r+1]$ put $B_{<i}=\{b_1,\dots,b_{i-1}\}$, $M_i=M/B_{<i}$ with rank function $r_i$, and $E_h^i=E_h\setminus B_{<i}$, where $E_h=\{e\in E:\ell(e)=h\}$. For $i\in[r]$ put
--   $$R_h^i=\{e\in E_h^i : c(e)\le c(b_i)\},\qquad H_i=\{h\in G : b_i\in \mathrm{cl}_{M_i}(R_h^i)\},$$
--   and set $R_h^{r+1}=E_h^{r+1}$. Then for every $i\in[r]$ and every $h\in G$,
--   $$r_i(R_h^i)-r_{i+1}(R_h^{i+1})\le \mathbf 1\{h\in H_i\}.$$
--
--   Contracting the next base element thus lowers the rank of each cost-filtered color class by at most one, and only for the colors in $H_i$. Combined with Corollary 11 this turns the count of labels into the rank sum of Theorem 4.
--
--   **Formalization Note** The ground set is the ground `M.E` of a Mathlib matroid on a finite type; subsets are `Finset`s and ranks are natural numbers. The Lean stage index $k$ is the source's $k+1$, so `i : Fin r` stands for $i+1\in[r]$, and the Lean stage $r$ is the terminal stage $r+1$, where `stageR` is the whole remaining color class. The integer difference inequality is written additively in $\mathbb N$.
--
--   Differences from the source:
--   - encoding: finite ground set E and subsets → Finset subsets of a finite ambient type with ground M.E and natural ranks; reason: every finite matroid admits this representation and finite ranks have no infinite case
--   - encoding: indices i ∈ [r] and terminal stage r+1 → i : Fin r represents source i+1 and natural stage k represents source k+1; H_i filtered over labels occurring on the ground; reason: stage arithmetic is a shift; a label not occurring on the ground has empty R_h^i, which cannot span the nonloop b_i, so no member of H_i is lost
--   - encoding: integer difference r_i(R_h^i) − r_{i+1}(R_h^{i+1}) ≤ 1{h ∈ H_i} → r_i(R_h^i) ≤ r_{i+1}(R_h^{i+1}) + 1{h ∈ H_i} in ℕ; reason: subtraction-free equivalent avoids truncated subtraction
-- source:
--   Siyue Liu, Taihei Oki, Chao Xu, Proximity Theorem and FPT Algorithm for Minimum Group-labeled Matroid Bases, STOC 2027 submission #554 (October 2026), p. 8, Lemma 12; standing hypotheses and definitions of M_i, r_i, R_h^i, H_i pp. 6–7 (§3, §3.1)

import Definitions.Def_GroupLabeledMatroid_Proximity_ContractionFiltration

namespace GroupLabeledMatroid.Proximity.Supplement

open GroupLabeledMatroid.Proximity

theorem filtered_rank_drop {E G : Type*} [Fintype E] [DecidableEq E] [AddCommGroup G] [DecidableEq G]
    (M : Matroid E) (ℓ : E → G) (c : E → ℝ) (B : Finset E)
    (hB : IsUniqueLabelMinimum M ℓ c B) {r : ℕ} (hr : 0 < r)
    (b : Fin r → E) (horder : IsCostOrder c B b) (i : Fin r) (h : G) :
    rankOn (stageMinor M b i.val) (stageR M ℓ c b i.val h) ≤
      rankOn (stageMinor M b (i.val + 1)) (stageR M ℓ c b (i.val + 1) h) +
        (if h ∈ stageH M ℓ c b i then 1 else 0) := by sorry

end GroupLabeledMatroid.Proximity.Supplement
