-- Prove2me | Theorems.Thm_GlobalTheory_cubeHomologyDirectSumEquiv_lof
-- name    : GlobalTheory.cubeHomologyDirectSumEquiv_lof
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:05.96359+00:00
-- url     : https://prove2.me/theorems/4fd8849f-dd43-5f37-ae36-4bb234385af0
-- title:
--   Global Theory: cube Homology Direct Sum Equiv lof
-- statement:
--   The Global Theory construction uses the cube Homology Direct Sum Equiv lof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L1114-L1119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L1114-L1119

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
open DirectSum
variable {R : Type u} [Ring R] {κ : Type} [DecidableEq κ]
variable {ι : Type}
variable [LinearOrder ι]
variable [Finite ι]

theorem GlobalTheory.cubeHomologyDirectSumEquiv_lof (A : κ → Cube.{v} ι R) (p : ℕ) (k : κ)
    (x : (cubeComplex (A k)).homology p) :
    cubeHomologyDirectSumEquiv A p
        (DirectSum.lof R κ (fun k => (cubeComplex (A k)).homology p) k x) =
      (HomologicalComplex.homologyMap (cubeComplexMap (Cube.directSumIncl A k)) p).hom x := by sorry
