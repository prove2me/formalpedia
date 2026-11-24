-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplex_exactAt_of_bijective
-- name    : GlobalTheory.cubeComplex_exactAt_of_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:34.685799+00:00
-- url     : https://prove2.me/theorems/def13701-bac5-4b51-a336-41a9fade1386
-- title:
--   Global Theory: cube Complex exact At of bijective
-- statement:
--   The Global Theory construction uses the cube Complex exact At of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L608-L618
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L608-L618

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

theorem GlobalTheory.cubeComplex_exactAt_of_bijective (A : Cube.{v} ι R) (i : ι)
    (hA : ∀ s : Finset ι, i ∉ s → Function.Bijective (Cube.res A (Finset.subset_insert i s)))
    (p : ℕ) : (cubeComplex A).ExactAt p := by sorry
