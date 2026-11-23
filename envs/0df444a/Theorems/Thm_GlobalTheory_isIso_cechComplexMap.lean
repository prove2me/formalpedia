-- Prove2me | Theorems.Thm_GlobalTheory_isIso_cechComplexMap
-- name    : GlobalTheory.isIso_cechComplexMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:10.212101+00:00
-- url     : https://prove2.me/theorems/22783833-0c74-48cc-b1d0-8383a2ea9eae
-- title:
--   Global Theory: is Iso cech Complex Map
-- statement:
--   The Global Theory construction uses the is Iso cech Complex Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L598-L606
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L598-L606

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

theorem GlobalTheory.isIso_cechComplexMap {A B : Cube.{v} ι R} (φ : A ⟶ B)
    (h : ∀ s : Finset ι, s.Nonempty → Function.Bijective (φ.app s).hom) :
    IsIso (cechComplexMap φ) := by sorry
