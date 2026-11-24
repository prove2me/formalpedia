-- Prove2me | Theorems.Thm_GlobalTheory_UnitDiscAlg_QuotAlg_comp1
-- name    : GlobalTheory.UnitDiscAlg.QuotAlg.comp1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:25:14.836395+00:00
-- url     : https://prove2.me/theorems/d6a92c1e-50f6-4361-a2ab-d2949fab8d0d
-- title:
--   Quot Alg: comp1
-- statement:
--   The Quot Alg construction uses the comp1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuotientIntegralUnit.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuotientIntegralUnit.lean#L22-L24

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

theorem GlobalTheory.UnitDiscAlg.QuotAlg.comp1 {e₁ e₂ e₃ : R} (h11 : e₁ * e₁ = e₁) (h12 : e₁ * e₂ = 0) (h13 : e₁ * e₃ = 0)
    (α β γ : R) : (α * e₁ + β * e₂ + γ * e₃) * e₁ = α * e₁ := by sorry
