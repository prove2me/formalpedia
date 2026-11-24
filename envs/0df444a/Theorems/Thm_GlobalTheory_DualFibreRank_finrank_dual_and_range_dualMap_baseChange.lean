-- Prove2me | Theorems.Thm_GlobalTheory_DualFibreRank_finrank_dual_and_range_dualMap_baseChange
-- name    : GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:51:53.732491+00:00
-- url     : https://prove2.me/theorems/7741b287-28d3-4e55-b865-07cc885b93fa
-- title:
--   Dual Fibre Rank: finrank dual and range dual Map base Change
-- statement:
--   The Dual Fibre Rank construction uses the finrank dual and range dual Map base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankDualAndRangeDualMapBaseChange.lean#L60-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankDualAndRangeDualMapBaseChange.lean#L60-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.DualFibreRank

theorem GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange :
    ∀ (O M N κ : Type) [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
      [Module.Finite O M] [Module.Projective O M] [Module.Finite O N] [Module.Projective O N]
      [Field κ] [Algebra O κ] (f : M →ₗ[O] N),
      Module.finrank κ (TensorProduct O κ (Module.Dual O M)) =
          Module.finrank κ (TensorProduct O κ M) ∧
        Module.finrank κ (LinearMap.range (f.dualMap.baseChange κ)) =
          Module.finrank κ (LinearMap.range (f.baseChange κ)) := by sorry
