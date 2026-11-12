-- Prove2me | Theorems.Thm_MultiAllocToAlloc_Subadditive_corollary_11_moreover_half_p
-- name    : MultiAllocToAlloc.Subadditive.corollary_11_moreover_half_p
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:21:46.699283+00:00
-- url     : https://prove2.me/theorems/afac1a7f-bef4-433d-a5b0-efa149f46033
-- title:
--   Corollary 11, parenthetical (corrected: ω(S_p, M, v) ≥ ½·MMS(M, v, 2))
-- statement:
--   Source (Feige, arXiv:2506.21493v1, Corollary 11, parenthetical, p. 8): ω(S_p, M, v) ≥ MMS(M, v, 2) for subadditive v, "following immediately from ω(S_p, M, v) ≥ ½v(M)". Variant: for every finite item set M and every normalized monotone subadditive valuation v, ω(S_p, M, v) ≥ ½·MMS(M, v, 2), where ω(S_p, M, v) is the maximin value of player p in the alternating picking game on M in which p picks first. Difference: the factor ½ is inserted (it follows from Proposition 8 and the corrected second sentence; ½·v(M) ≥ MMS(M, v, 2) fails for subadditive v), and the hypothesis on δ is dropped.
-- source:
--   Feige, arXiv:2506.21493v1, Corollary 11, p. 8 (corrected)

import Mathlib
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_PickingGame

theorem MultiAllocToAlloc.Subadditive.corollary_11_moreover_half_p {m : ℕ} (M : Finset (Fin m))
    (v : Finset (Fin m) → ℝ) (hnorm : MultiAllocToAlloc.Subadditive.IsNormalized v)
    (hmono : MultiAllocToAlloc.Subadditive.IsMonotone v) (hsub : SubmodOrder.Subadditive v) :
    LittleCharity.MMS.mms v 2 M / 2 ≤ MultiAllocToAlloc.Subadditive.omegaP v M := by sorry
