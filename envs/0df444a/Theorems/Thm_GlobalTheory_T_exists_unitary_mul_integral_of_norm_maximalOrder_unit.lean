-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_unitary_mul_integral_of_norm_maximalOrder_unit
-- name    : GlobalTheory.T.exists_unitary_mul_integral_of_norm_maximalOrder_unit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:02.839391+00:00
-- url     : https://prove2.me/theorems/d7354273-525e-462e-bd9f-03db01e56351
-- title:
--   T: exists unitary mul integral of norm maximal Order unit
-- statement:
--   The T construction uses the exists unitary mul integral of norm maximal Order unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryMulIntegralOfNormMaximalOrderUnitStatement.lean#L8-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryMulIntegralOfNormMaximalOrderUnitStatement.lean#L8-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnit
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnitStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_unitary_mul_integral_of_norm_maximalOrder_unit : ∀ {O K A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Algebra K A] [Algebra O A] [IsScalarTower O K A] [Module.Finite K A] [IsReduced A]
    (σ : K →+* K), (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    ∀ τ : A →+* A, (∀ a, τ (τ a) = a) → (∀ k, τ (algebraMap K A k) = algebraMap K A (σ k)) →
    ∀ x : Aˣ, IsIntegral O (τ (x : A) * x) → IsIntegral O (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A)) →
    ∃ t : Aˣ, τ (t : A) * t = 1 ∧ IsIntegral O ((t : A) * ((x⁻¹ : Aˣ) : A)) ∧
      IsIntegral O (((t⁻¹ : Aˣ) : A) * (x : A)) := by sorry
