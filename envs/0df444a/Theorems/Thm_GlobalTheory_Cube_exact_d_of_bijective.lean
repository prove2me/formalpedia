-- Prove2me | Theorems.Thm_GlobalTheory_Cube_exact_d_of_bijective
-- name    : GlobalTheory.Cube.exact_d_of_bijective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:18.847506+00:00
-- url     : https://prove2.me/theorems/1efbe305-cc6c-4a31-afc2-c8c9832d68b4
-- title:
--   Cube: exact d of bijective
-- statement:
--   The Cube construction uses the exact d of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L336-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L336-L361

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
open GlobalTheory.Cube
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]

theorem GlobalTheory.Cube.exact_d_of_bijective (A : Cube.{v} ι R) (i : ι)
    (hA : ∀ s : Finset ι, i ∉ s → Function.Bijective (res A (Finset.subset_insert i s))) (p : ℕ) :
    Function.Exact (d A p) (d A (p + 1)) := by sorry
