-- Prove2me | Theorems.Thm_GlobalTheory_cechCyclesIso_hom_subtype
-- name    : GlobalTheory.cechCyclesIso_hom_subtype
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:52.709788+00:00
-- url     : https://prove2.me/theorems/62b0510b-828e-442f-99fd-5a976786a652
-- title:
--   Global Theory: cech Cycles Iso hom subtype
-- statement:
--   The Global Theory construction uses the cech Cycles Iso hom subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L533-L536
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L533-L536

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]

theorem GlobalTheory.cechCyclesIso_hom_subtype (A : Cube.{v} ι R) (p : ℕ) :
    (cechCyclesIso A p).hom ≫ ModuleCat.ofHom (LinearMap.ker (Cube.d A (p + 1))).subtype =
      (cechComplex A).iCycles p := by sorry
