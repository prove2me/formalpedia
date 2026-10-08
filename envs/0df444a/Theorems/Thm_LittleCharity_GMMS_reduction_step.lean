-- Prove2me | Theorems.Thm_LittleCharity_GMMS_reduction_step
-- name    : LittleCharity.GMMS.reduction_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:41.475224+00:00
-- url     : https://prove2.me/theorems/92b3811d-088b-42e9-b357-c8c9e0156cf6
-- title:
--   Proof of Theorem 16 — one reduction step for excess bad goods
-- statement:
--   Fix an agent $i$ with a nonnegative additive valuation, a finite good set $S$, and a distinguished subset $B\subseteq S$ of bad goods. If a maximin-share partition uses $k\ge2$ parts and $|B|>k$, then two distinct bad goods $g_1,g_2\in B$ can be removed while reducing the number of parts by one without lowering the share:
--
--   $$
--   \operatorname{MMS}_i(k,S)\le
--   \operatorname{MMS}_i(k-1,S\setminus\{g_1,g_2\}).
--   $$
--
--   This is the numerical reduction applied repeatedly in the proof of Theorem 16 until the number of bad goods is no greater than the number of parts.
--
--   **Formalization Note** The paper's loop has $k\ge2$ at each such step; this explicit guard also keeps the maximin share away from a zero-part partition and makes $k-1$ ordinary natural-number subtraction.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, p. 16, proof of Theorem 16, reduction step

import Mathlib
import Definitions.Def_LittleCharity_GMMS_Setting

namespace LittleCharity.GMMS

/-- Proof of Theorem 16, p. 16: remove two bad goods and one MMS part without reducing the share. -/
theorem reduction_step {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : LittleCharity.MMS.IsAdditive v)
    (i : Fin n) (k : ℕ) (hk : 2 ≤ k) (S B : Finset (Fin m))
    (hB : B ⊆ S) (hcard : k < B.card) :
    ∃ g₁ ∈ B, ∃ g₂ ∈ B, g₁ ≠ g₂ ∧
      LittleCharity.MMS.mms (v i) k S ≤ LittleCharity.MMS.mms (v i) (k - 1) (S \ {g₁, g₂}) := by sorry

end LittleCharity.GMMS
