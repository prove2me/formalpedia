-- Prove2me | Theorems.Thm_GlobalTheory_SymmProd_zpow_finsum_eq
-- name    : GlobalTheory.SymmProd.zpow_finsum_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:09.633625+00:00
-- url     : https://prove2.me/theorems/0d371bcb-b43b-4253-9f6f-31661a37d0f3
-- title:
--   Symm Prod: zpow finsum eq
-- statement:
--   The Symm Prod construction uses the zpow finsum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdFourMapsEqOne.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdFourMapsEqOne.lean#L7-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdFourMapsEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SymmProd
open scoped Matrix

theorem GlobalTheory.SymmProd.zpow_finsum_eq {U : Type} [CommGroup U] {ι : Type} (s : Finset ι) (x : U) (f : ι → ℤ) :
    x ^ (∑ i ∈ s, f i) = ∏ i ∈ s, x ^ f i := by sorry
