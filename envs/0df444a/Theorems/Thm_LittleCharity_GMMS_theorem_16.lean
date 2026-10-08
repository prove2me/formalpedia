-- Prove2me | Theorems.Thm_LittleCharity_GMMS_theorem_16
-- name    : LittleCharity.GMMS.theorem_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:25.547982+00:00
-- url     : https://prove2.me/theorems/a454de5d-7ad4-48b1-ae00-7e57e0c64d83
-- title:
--   Theorem 16 — pool donation gives a complete 4/7-GMMS allocation
-- statement:
--   Let agents have nonnegative additive valuations. Start from a partial allocation $X$ that is EFX and satisfies $v_i(P)\le v_i(X_i)$ for every agent $i$, where $P$ is exactly its unallocated pool. Let $s$ be an unenvied agent, and form $Y$ by giving all of $P$ to $s$ while leaving the other bundles unchanged. Then $Y$ is complete, every agent's own value is at least its value under $X$, and
--
--   $$
--   v_i(Y_i)\ge\frac47\operatorname{MMS}_i\!\left(|N'|,\bigcup_{j\in N'}Y_j\right)
--   \quad\text{for every }N'\subseteq N\text{ and }i\in N'.
--   $$
--
--   Thus donating the pool to an unenvied agent yields the paper's $4/7$ groupwise maximin-share guarantee for the complete allocation constructed on p. 15.
--
--   **Formalization Note** The paper obtains $X$ from Lemma 12 and writes “without loss of generality, agent 1 is a source.” Here the result is stated for every $X$ with the EFX and pool-value properties used in the proof, and for every named source $s$. Theorem 8 supplies such an $X$ and a source. The paper's additional half-optimal-Nash-social-welfare bullet relies on the black-box guarantee of Lemma 12 and is not posed here; the theorem records the proof's value-monotonicity step $v_i(Y_i)\ge v_i(X_i)$. The factor $4/7$ is real-valued.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, pp. 15–17, Definition 15, constructed allocation, Theorem 16 (GMMS bullet) and proof

import Mathlib
import Definitions.Def_LittleCharity_GMMS_Setting

namespace LittleCharity.GMMS

/-- Theorem 16, pp. 15–16, GMMS bullet, for the source allocation after donation. -/
theorem theorem_16 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : LittleCharity.MMS.IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hX : LittleCharity.EFX.IsPartialAllocation X) (hEFX : LittleCharity.MMS.IsEFX v X)
    (hpool : ∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i))
    (s : Fin n) (hs : LittleCharity.EFX.IsSource v X s) :
    IsCompleteAllocation (donate X s) ∧ IsGMMS (4 / 7 : ℝ) v (donate X s) ∧
      ∀ i, v i (X i) ≤ v i (donate X s i) := by sorry

end LittleCharity.GMMS
