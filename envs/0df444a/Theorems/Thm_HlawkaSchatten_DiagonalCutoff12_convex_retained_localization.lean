-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_convex_retained_localization
-- name    : HlawkaSchatten.DiagonalCutoff12.convex_retained_localization
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T00:24:45.768643+00:00
-- url     : https://prove2.me/theorems/e6ec863b-df68-4e39-8779-84f9fb636537
-- title:
--   Convex norm-budget and row-ratio constraints for Hlawka averaging
-- statement:
--   Let $p\ge1$, $\tau,s\ge0$, and $R\in\mathbb R$. For triples $X=(X_0,X_1,X_2)\in(\mathbb R^3)^3$, define the domain by
--   $$\sum_i\|X_i\|_p\le R,$$
--   $$\tau\|X_i\|_p\le X_i(j)\quad(i\ne j),$$
--   $$s\|X_i\|_p\le X_i(j)+X_i(k)\quad(\{i,j,k\}=\{0,1,2\}).$$
--   This domain is convex. These inequalities may therefore be retained during simultaneous vector-coordinate averaging, once they have been established in the localization stage. In particular, normalization to a norm sum of 3 allows the convex inequality with $R=3$ to be kept.
-- source:
--   Original structural improvement for the sharp diagonal Hlawka cutoff-2 campaign, with cutoff 12 under investigation: https://prove2.me/theorems/7fe6f02d-65e5-4c21-9796-c83889b29b9d . Generic coordinate-norm arguments retain attribution to the Apache-2.0 Prove2Me contributions of Ezzeri Esa, bwdaugherty and Yuxuan Xu; this result is a supporting lemma, not a claim that cutoff 12 is proved.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Analysis.Convex.Function
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem HlawkaSchatten.DiagonalCutoff12.convex_retained_localization {p τ s : ℝ}
    (hp : 1 ≤ p) (hτ : 0 ≤ τ) (hs : 0 ≤ s) (R : ℝ) :
    Convex ℝ {X : Fin 3 → Fin 3 → ℝ |
      (∑ j, lpNorm p (X j)) ≤ R ∧
      (∀ j i, j ≠ i → τ*lpNorm p (X j) ≤ X j i) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        s*lpNorm p (X i) ≤ X i j+X i k)} := by sorry
