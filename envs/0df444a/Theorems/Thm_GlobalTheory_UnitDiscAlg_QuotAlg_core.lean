-- Prove2me | Theorems.Thm_GlobalTheory_UnitDiscAlg_QuotAlg_core
-- name    : GlobalTheory.UnitDiscAlg.QuotAlg.core
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:25:53.260152+00:00
-- url     : https://prove2.me/theorems/93d90599-2fad-4e29-967d-8d8e3b51f3d5
-- title:
--   Quot Alg: core
-- statement:
--   The Quot Alg construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuotientIntegralUnit.lean#L34-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuotientIntegralUnit.lean#L34-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDetLeOneOfEntriesNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitAndIntegInvOfNormDetEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuotientIntegralUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.UnitDiscAlg GlobalTheory.UnitDiscAlg.QuotAlg
variable {R : Type*} [CommRing R]

theorem GlobalTheory.UnitDiscAlg.QuotAlg.core (p pi c ci u a₂ a₃ b e₁ e₂ e₃ k11 k12 k13 k21 k22 k23 k31 k32 k33 k41 k42 k43 : R)
    (hp : p * pi = 1) (hci : c * ci = 1)
    (h11 : e₁ * e₁ = e₁) (h22 : e₂ * e₂ = e₂) (h33 : e₃ * e₃ = e₃)
    (h12 : e₁ * e₂ = 0) (h13 : e₁ * e₃ = 0) (h23 : e₂ * e₃ = 0) (hs : e₁ + e₂ + e₃ = 1)
    (hc1 : c * e₁ = u * e₁) (hc2 : c * e₂ = p * (a₂ * e₂)) (hc3 : ci * e₃ = p * (a₃ * e₃))
    (hk11 : (p + u ^ 2) * k11 = 1) (hk12 : (1 + p * a₂ ^ 2) * k12 = 1)
    (hk13 : (1 + p ^ 3 * a₃ ^ 2) * k13 = 1)
    (hk21 : (p + u ^ 3) * k21 = 1) (hk22 : (1 + p ^ 2 * a₂ ^ 3) * k22 = 1)
    (hk23 : (1 + p ^ 4 * a₃ ^ 3) * k23 = 1)
    (hk31 : (p * u ^ 2 + b ^ 2) * k31 = 1) (hk32 : (b ^ 2 + p ^ 3 * a₂ ^ 2) * k32 = 1)
    (hk33 : (1 + p * b ^ 2 * a₃ ^ 2) * k33 = 1)
    (hk41 : (p * u ^ 3 + b ^ 3) * k41 = 1) (hk42 : (b ^ 3 + p ^ 4 * a₂ ^ 3) * k42 = 1)
    (hk43 : (1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * k43 = 1) :
    (p + c ^ 2) * (k11 * e₁ + (pi * k12) * e₂ + (ci ^ 2 * k13) * e₃) = 1 ∧
    (p + c ^ 3) * (k21 * e₁ + (pi * k22) * e₂ + (ci ^ 3 * k23) * e₃) = 1 ∧
    (p * c ^ 2 + b ^ 2) * (k31 * e₁ + k32 * e₂ + (pi * ci ^ 2 * k33) * e₃) = 1 ∧
    (p * c ^ 3 + b ^ 3) * (k41 * e₁ + k42 * e₂ + (pi * ci ^ 3 * k43) * e₃) = 1 ∧
    (p * c ^ 3 + b ^ 3) * (p + c ^ 2) =
      (((p * u ^ 3 + b ^ 3) * (p + u ^ 2) * k21 * k31) * e₁
        + ((b ^ 3 + p ^ 4 * a₂ ^ 3) * (1 + p * a₂ ^ 2) * k22 * k32) * e₂
        + ((1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * (1 + p ^ 3 * a₃ ^ 2) * k23 * k33) * e₃)
        * ((p + c ^ 3) * (p * c ^ 2 + b ^ 2)) ∧
    (((p * u ^ 3 + b ^ 3) * (p + u ^ 2) * k21 * k31) * e₁
        + ((b ^ 3 + p ^ 4 * a₂ ^ 3) * (1 + p * a₂ ^ 2) * k22 * k32) * e₂
        + ((1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * (1 + p ^ 3 * a₃ ^ 2) * k23 * k33) * e₃) *
      (((p + u ^ 3) * (p * u ^ 2 + b ^ 2) * k41 * k11) * e₁
        + ((1 + p ^ 2 * a₂ ^ 3) * (b ^ 2 + p ^ 3 * a₂ ^ 2) * k42 * k12) * e₂
        + ((1 + p ^ 4 * a₃ ^ 3) * (1 + p * b ^ 2 * a₃ ^ 2) * k43 * k13) * e₃) = 1 := by sorry
