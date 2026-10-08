-- Prove2me | Theorems.Thm_LittleCharity_GMMS_lemma_17_c
-- name    : LittleCharity.GMMS.lemma_17_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:28.175172+00:00
-- url     : https://prove2.me/theorems/586b141c-736a-42ef-9df9-73cd529d2560
-- title:
--   Lemma 17(c) — a good bundle is worth at most three halves of one's own
-- statement:
--   Let $X$ be a partial EFX allocation for nonnegative additive valuations. Suppose every agent values the pool no more than its own bundle, and $s$ is an unenvied agent. Give the pool to $s$, obtaining $Y$. Fix an observing agent $i$. If $j\ne s$ and either $j=i$ or $Y_j$ contains at least three goods, then
--
--   $$
--   v_i(Y_j)\le\frac32v_i(Y_i).
--   $$
--
--   These are exactly the good bundles other than the donor's bundle in the classification before Lemma 17. Their value bound is used in the final count of Theorem 16.
--
--   **Formalization Note** The page's “agent 1” is $s$. The disjunction also covers $j=i$, whose own bundle is classified as good at any size.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, pp. 16–17, classification and Lemma 17(c)

import Mathlib
import Definitions.Def_LittleCharity_GMMS_Setting

namespace LittleCharity.GMMS

/-- Lemma 17(c), p. 16: a good bundle other than the source's has value at most three halves of one's own. -/
theorem lemma_17_c {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : LittleCharity.MMS.IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hX : LittleCharity.EFX.IsPartialAllocation X) (hEFX : LittleCharity.MMS.IsEFX v X)
    (hpool : ∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i))
    (s : Fin n) (hs : LittleCharity.EFX.IsSource v X s) (i : Fin n) :
    ∀ j, j ≠ s → (3 ≤ (donate X s j).card ∨ j = i) →
      v i (donate X s j) ≤ (3 / 2 : ℝ) * v i (donate X s i) := by sorry

end LittleCharity.GMMS
