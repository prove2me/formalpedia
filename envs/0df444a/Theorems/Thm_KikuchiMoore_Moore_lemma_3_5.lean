-- Prove2me | Theorems.Thm_KikuchiMoore_Moore_lemma_3_5
-- name    : KikuchiMoore.Moore.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:41:54.042209+00:00
-- url     : https://prove2.me/theorems/98bf7085-3994-4e23-a919-2e64f629dafb
-- title:
--   Lemma 3.5 — Orientation bound including nonnegative weights
-- statement:
--   Let $I,X$ be finite index sets, $A$ a nonnegative real base matrix with realized mean degree $\bar d>0$, and $p:X\to I$ a row projection. Let $T_{xy}\ge0$ be directed raw lift weights and $W_{xy}=T_{xy}+T_{yx}$. Assume $\sum_y W_{xy}\le d(p(x))$ for each state. For any $\kappa\ge0$, if $\sum_y T_{yx}\le\kappa$ for every state, the inherited normalized lift satisfies
--
--   $$\|L\|_{2\to2}\le2\sqrt{\kappa/\bar d}.$$
--
--   This includes the source's ordinary oriented lift with unit weights and its nonnegative weighted extension. Parallel oriented edges are summed into $T$; the bound uses incoming raw weight, not normalized matrix entries.
--
--   Differences from the source:
--   - generalization: the concrete truncated lift, with unit or nonnegative edge weights → arbitrary finite nonnegative weighted lift matrices with a row projection and local degree domination; reason: every source lift has this domination because each lifted incident edge projects injectively to a base incident edge; the source proof uses only these structural conditions
--   - encoding: an orientation of weighted lift edges → a nonnegative directed matrix T with W = T + transpose T; reason: summing oriented parallel edges preserves incoming weights and normalization; unit weights give the unweighted case
--   - encoding: an in-degree (incoming-weight) bound κ → a real κ with hypothesis 0 ≤ κ; reason: in-degrees and incoming weights are nonnegative, so every source κ satisfies it; it excludes only negative κ on an empty state type, which no source lift has
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Lemma 3.5, printed p. 14 = PDF p. 14, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Operators

open scoped BigOperators

namespace KikuchiMoore.Moore

theorem lemma_3_5 {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    (A : Matrix I I ℝ) (row : X → I) (W T : Matrix X X ℝ) (κ : ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hmean : 0 < meanDegree A)
    (hT : ∀ x y, 0 ≤ T x y)
    (horient : ∀ x y, W x y = T x y + T y x)
    (hlift : ∀ x, (∑ y, W x y) ≤ degree A (row x))
    (hin : ∀ x, (∑ y, T y x) ≤ κ) (hκ : 0 ≤ κ) :
    opNorm (normalizedLift A row W) ≤ 2 * Real.sqrt (κ / meanDegree A) := by sorry

end KikuchiMoore.Moore
