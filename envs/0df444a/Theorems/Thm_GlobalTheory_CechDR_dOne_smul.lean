-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_dOne_smul
-- name    : GlobalTheory.CechDR.dOne_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:01.902023+00:00
-- url     : https://prove2.me/theorems/6adf24c6-2429-4eb0-b012-f20b7e980433
-- title:
--   Cech DR: d One smul
-- statement:
--   The Cech DR construction uses the d One smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L329-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L329-L331

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

theorem GlobalTheory.CechDR.dOne_smul (b : B) (ω : Ω[B⁄R]) :
    dOne R B (b • ω) = wedge R B (D R B b) ω + b • dOne R B ω := by sorry
