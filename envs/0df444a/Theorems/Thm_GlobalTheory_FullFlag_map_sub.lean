-- Prove2me | Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- name    : GlobalTheory.FullFlag.map_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:41.537944+00:00
-- url     : https://prove2.me/theorems/945d3358-c47d-4480-a1af-2ea91f80c260
-- title:
--   Full Flag: map sub
-- statement:
--   The Full Flag construction uses the map sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L381-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L381-L382

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.FullFlag
variable {n : ℕ}

theorem GlobalTheory.FullFlag.map_sub {M' : Type*} [AddCommGroup M'] [Module R M'] (F : FullFlag R M n)
    (e : M ≃ₗ[R] M') (k : Fin (n + 1)) : (F.map e).sub k = (F.sub k).map e.toLinearMap := by sorry

attribute [defeq] GlobalTheory.FullFlag.map_sub
