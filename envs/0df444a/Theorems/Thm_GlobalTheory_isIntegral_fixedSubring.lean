-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_fixedSubring
-- name    : GlobalTheory.isIntegral_fixedSubring
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:28.633969+00:00
-- url     : https://prove2.me/theorems/b5568bc3-7f37-4e2f-aafd-6ee9629e1451
-- title:
--   Global Theory: is Integral fixed Subring
-- statement:
--   The Global Theory construction uses the is Integral fixed Subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L25-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (A G : Type*) [CommRing A] [Group G] [MulSemiringAction G A]

theorem GlobalTheory.isIntegral_fixedSubring [Finite G] : Algebra.IsIntegral (FixedPoints.subring A G) A := by sorry
