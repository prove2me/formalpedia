-- Prove2me | Theorems.Thm_GlobalTheory_cechHomologyDirectSumEquiv_lof
-- name    : GlobalTheory.cechHomologyDirectSumEquiv_lof
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:43:46.597019+00:00
-- url     : https://prove2.me/theorems/ae2c640b-a34d-477b-9069-c9127659d4b9
-- title:
--   Global Theory: cech Homology Direct Sum Equiv lof
-- statement:
--   The Global Theory construction uses the cech Homology Direct Sum Equiv lof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L1130-L1135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L1130-L1135

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

theorem GlobalTheory.cechHomologyDirectSumEquiv_lof (A : κ → Cube.{v} ι R) (p : ℕ) (k : κ)
    (x : (cechComplex (A k)).homology p) :
    cechHomologyDirectSumEquiv A p
        (DirectSum.lof R κ (fun k => (cechComplex (A k)).homology p) k x) =
      (HomologicalComplex.homologyMap (cechComplexMap (Cube.directSumIncl A k)) p).hom x := by sorry
