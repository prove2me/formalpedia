-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_dOne_smul_D
-- name    : GlobalTheory.CechDR.dOne_smul_D
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:07:57.563622+00:00
-- url     : https://prove2.me/theorems/f8c779ba-096d-4c9f-b926-ca87a177e376
-- title:
--   Cech DR: d One smul D
-- statement:
--   The Cech DR construction uses the d One smul D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L333-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L333-L334

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
variable {R B}

theorem GlobalTheory.CechDR.dOne_smul_D (b c : B) : dOne R B (b • D R B c) = wedge R B (D R B b) (D R B c) := by sorry
