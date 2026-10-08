-- Prove2me | Theorems.Thm_LittleCharity_GMMS_lemma_17_a
-- name    : LittleCharity.GMMS.lemma_17_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:19.232226+00:00
-- url     : https://prove2.me/theorems/dcedf63d-8de3-4804-ae29-0ee7fec1de0c
-- title:
--   Lemma 17(a) — each bad good is worth at most one's own bundle
-- statement:
--   Let $X$ be a partial EFX allocation for nonnegative additive valuations. Suppose every agent values its pool no more than its own bundle, and $s$ is an unenvied agent. Form $Y$ by giving the pool to $s$. For any observer $i$, a **bad good** $g$ lies in a two-good bundle $Y_j$ with $j\ne s$ and $j\ne i$. Then
--
--   $$
--   v_i(\{g\})\le v_i(Y_i).
--   $$
--
--   This bounds the aggregate value of bad goods in the proof of the $4/7$ guarantee.
--
--   **Formalization Note** The page calls the donor “agent 1”; Lean uses a named source $s$. A bad good is encoded through its containing bundle, following the classification immediately before Lemma 17.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, p. 16, classification and Lemma 17(a)

import Mathlib
import Definitions.Def_LittleCharity_GMMS_Setting

namespace LittleCharity.GMMS

/-- Lemma 17(a), p. 16: each bad good is worth at most the observing agent's own bundle. -/
theorem lemma_17_a {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : LittleCharity.MMS.IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hX : LittleCharity.EFX.IsPartialAllocation X) (hEFX : LittleCharity.MMS.IsEFX v X)
    (hpool : ∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i))
    (s : Fin n) (hs : LittleCharity.EFX.IsSource v X s) (i : Fin n) :
    ∀ j, j ≠ s → j ≠ i → (donate X s j).card = 2 →
      ∀ g ∈ donate X s j, v i {g} ≤ v i (donate X s i) := by sorry

end LittleCharity.GMMS
