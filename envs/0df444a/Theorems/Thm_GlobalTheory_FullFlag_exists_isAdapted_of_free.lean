-- Prove2me | Theorems.Thm_GlobalTheory_FullFlag_exists_isAdapted_of_free
-- name    : GlobalTheory.FullFlag.exists_isAdapted_of_free
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:21.661705+00:00
-- url     : https://prove2.me/theorems/125540bc-7102-4161-aee5-b97c71dcf9ae
-- title:
--   Full Flag: exists is Adapted of free
-- statement:
--   The Full Flag construction uses the exists is Adapted of free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L391-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L391-L438

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

theorem GlobalTheory.FullFlag.exists_isAdapted_of_free (F : FullFlag R M n) (h : ∀ i, Module.Free R (F.Step i)) :
    ∃ b : Basis (Fin n) R M, F.IsAdapted b := by sorry
