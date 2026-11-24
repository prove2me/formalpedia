-- Prove2me | Theorems.Thm_GlobalTheory_FullFlag_isAdapted_iff
-- name    : GlobalTheory.FullFlag.isAdapted_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:40:07.830985+00:00
-- url     : https://prove2.me/theorems/7cdfea41-9ba2-4257-a404-1cd9712caeac
-- title:
--   Full Flag: is Adapted iff
-- statement:
--   The Full Flag construction uses the is Adapted iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L249-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L249-L250

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

theorem GlobalTheory.FullFlag.isAdapted_iff {F : FullFlag R M n} {b : Basis (Fin n) R M} :
    F.IsAdapted b ↔ ofBasis b = F := by sorry
