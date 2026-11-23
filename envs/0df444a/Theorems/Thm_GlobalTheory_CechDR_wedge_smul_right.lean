-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_wedge_smul_right
-- name    : GlobalTheory.CechDR.wedge_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:29.361667+00:00
-- url     : https://prove2.me/theorems/f2fcd48e-f98c-4dc5-ae84-bf07cbbd9b87
-- title:
--   Cech DR: wedge smul right
-- statement:
--   The Cech DR construction uses the wedge smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L322-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L322-L323

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

theorem GlobalTheory.CechDR.wedge_smul_right (r : R) (a b : Ω[B⁄R]) : wedge R B a (r • b) = r • wedge R B a b := by sorry
