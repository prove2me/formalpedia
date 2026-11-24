-- Prove2me | Theorems.Thm_GlobalTheory_ordTop_vw_unit_mul_zpow
-- name    : GlobalTheory.ordTop_vw_unit_mul_zpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:54.086583+00:00
-- url     : https://prove2.me/theorems/8ba6d1c3-ee7d-4735-8a7c-7935895108a4
-- title:
--   Global Theory: ord Top vw unit mul zpow
-- statement:
--   The Global Theory construction uses the ord Top vw unit mul zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L253-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L253-L260

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (V : Type*) {F : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F]
variable {V}

theorem GlobalTheory.ordTop_vw_unit_mul_zpow {t : V} (ht : Irreducible t) (u : Vˣ) (m : ℤ) :
    ordTop_vw V (algebraMap V F u * algebraMap V F t ^ m) = m := by sorry
