-- Prove2me | Theorems.Thm_GlobalTheory_isFiniteLength_restrictScalars_of_finite
-- name    : GlobalTheory.isFiniteLength_restrictScalars_of_finite
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:47:05.962891+00:00
-- url     : https://prove2.me/theorems/d3fb0719-72d0-5a22-b547-7039f2ae9b5f
-- title:
--   Global Theory: is Finite Length restrict Scalars of finite
-- statement:
--   The Global Theory construction uses the is Finite Length restrict Scalars of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L283-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L283-L291

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]

theorem GlobalTheory.isFiniteLength_restrictScalars_of_finite [Module.Finite R S] {X : Type*} [AddCommGroup X]
    [Module S X] (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X] :
    IsFiniteLength R X := by sorry
