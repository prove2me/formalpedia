-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLat_exists_mul_isIntegral
-- name    : GlobalTheory.UnitLemma.PrincipalLat.exists_mul_isIntegral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:06.725654+00:00
-- url     : https://prove2.me/theorems/116bef21-a9e2-4d7c-8b93-8309250b0f1d
-- title:
--   Principal Lat: exists mul is Integral
-- statement:
--   The Principal Lat construction uses the exists mul is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqMulIntegralClosureOfSeparableInvolutionAlgebra.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqMulIntegralClosureOfSeparableInvolutionAlgebra.lean#L32-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PrincipalLat
variable {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
  [CommRing A] [Algebra E A] [Algebra O A] [IsScalarTower O E A] [Module.Finite E A]
variable (E)
include E

theorem GlobalTheory.UnitLemma.PrincipalLat.exists_mul_isIntegral (y : A) : ∃ c : O, c ≠ 0 ∧ IsIntegral O (algebraMap O A c * y) := by sorry
