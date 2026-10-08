-- Prove2me | Theorems.Thm_LittleCharity_GMMS_lemma_17_b
-- name    : LittleCharity.GMMS.lemma_17_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:21.504158+00:00
-- url     : https://prove2.me/theorems/772f7a1d-d896-4b8f-a12f-856c36bd6538
-- title:
--   Lemma 17(b) — the donor's bundle is worth at most twice one's own
-- statement:
--   Let $X$ be a partial EFX allocation for nonnegative additive valuations. Suppose every agent values the pool no more than its own bundle, and $s$ is an unenvied agent. Give the pool to $s$, obtaining $Y$. Then every agent $i$ satisfies
--
--   $$
--   v_i(Y_s)\le2v_i(Y_i).
--   $$
--
--   This controls the one bundle enlarged by the donation in the proof of Theorem 16.
--
--   **Formalization Note** Unenvied means no agent has an envy edge toward $s$; it does not mean that $s$ envies nobody. The source's “agent 1” is the named source $s$.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, pp. 16–17, Lemma 17(b)

import Mathlib
import Definitions.Def_LittleCharity_GMMS_Setting

namespace LittleCharity.GMMS

/-- Lemma 17(b), p. 16: the source's donated bundle is worth at most twice one's own. -/
theorem lemma_17_b {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : LittleCharity.MMS.IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hX : LittleCharity.EFX.IsPartialAllocation X) (hEFX : LittleCharity.MMS.IsEFX v X)
    (hpool : ∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i))
    (s : Fin n) (hs : LittleCharity.EFX.IsSource v X s) (i : Fin n) :
    v i (donate X s s) ≤ 2 * v i (donate X s i) := by sorry

end LittleCharity.GMMS
