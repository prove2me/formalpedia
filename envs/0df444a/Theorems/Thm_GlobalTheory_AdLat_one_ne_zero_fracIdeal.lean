-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_one_ne_zero_fracIdeal
-- name    : GlobalTheory.AdLat.one_ne_zero_fracIdeal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:07:00.993135+00:00
-- url     : https://prove2.me/theorems/983daadd-a4be-4386-8839-277e7fa25af7
-- title:
--   Ad Lat: one ne zero frac Ideal
-- statement:
--   The Ad Lat construction uses the one ne zero frac Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FiniteAdeleStrongApproximationModNat.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FiniteAdeleStrongApproximationModNat.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat

theorem GlobalTheory.AdLat.one_ne_zero_fracIdeal (F : Type) [Field F] [NumberField F] :
    (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by sorry
