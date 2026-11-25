-- Prove2me | Theorems.Thm_GlobalTheory_FullFlag_ofBasis_map
-- name    : GlobalTheory.FullFlag.ofBasis_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:35.954819+00:00
-- url     : https://prove2.me/theorems/34a06d11-cacd-5277-b358-cbc5193ec7a9
-- title:
--   Full Flag: of Basis map
-- statement:
--   The Full Flag construction uses the of Basis map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L384-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L384-L389

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

theorem GlobalTheory.FullFlag.ofBasis_map {M' : Type*} [AddCommGroup M'] [Module R M'] (b : Basis (Fin n) R M)
    (e : M ≃ₗ[R] M') : ofBasis (b.map e) = (ofBasis b).map e := by sorry
