-- Prove2me | Theorems.Thm_MultiAllocToAlloc_Subadditive_corollary_11_moreover_half_q
-- name    : MultiAllocToAlloc.Subadditive.corollary_11_moreover_half_q
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:21:01.754528+00:00
-- url     : https://prove2.me/theorems/de7069c9-663e-4541-a313-dc7988a2e743
-- title:
--   Corollary 11, second sentence (corrected: ω(S_q, M, v) ≥ ½·MMS(M, v, 2))
-- statement:
--   Source (Feige, arXiv:2506.21493v1, Corollary 11, second sentence, p. 8): if v is subadditive and no single item has value larger than δ, then ω(S_q, M, v) ≥ MMS(M, v, 2). Variant: for every finite item set M and every normalized monotone subadditive valuation v, ω(S_q, M, v) ≥ ½·MMS(M, v, 2), where ω(S_q, M, v) is the maximin value of player p in the alternating picking game on M in which q picks first and MMS(M, v, 2) is the maximin share of M over partitions into two (possibly empty) bundles. Difference: the factor ½ is inserted (the proof on p. 8 gives ω(S_q, M, v) = ω(S_p, M′, v) ≥ ½·v(M′) ≥ ½·MMS(M, v, 2)), and the hypothesis on δ, which this clause does not use, is dropped.
-- source:
--   Feige, arXiv:2506.21493v1, Corollary 11, p. 8 (corrected)

import Mathlib
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_PickingGame

theorem MultiAllocToAlloc.Subadditive.corollary_11_moreover_half_q {m : ℕ} (M : Finset (Fin m))
    (v : Finset (Fin m) → ℝ) (hnorm : MultiAllocToAlloc.Subadditive.IsNormalized v)
    (hmono : MultiAllocToAlloc.Subadditive.IsMonotone v) (hsub : SubmodOrder.Subadditive v) :
    LittleCharity.MMS.mms v 2 M / 2 ≤ MultiAllocToAlloc.Subadditive.omegaQ v M := by sorry
