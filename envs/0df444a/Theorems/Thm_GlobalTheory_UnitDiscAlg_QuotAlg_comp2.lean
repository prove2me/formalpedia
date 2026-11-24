-- Prove2me | Theorems.Thm_GlobalTheory_UnitDiscAlg_QuotAlg_comp2
-- name    : GlobalTheory.UnitDiscAlg.QuotAlg.comp2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:25:42.657101+00:00
-- url     : https://prove2.me/theorems/b67cdcbd-f1c8-4f59-81ac-5bb6edab61bb
-- title:
--   Quot Alg: comp2
-- statement:
--   The Quot Alg construction uses the comp2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuotientIntegralUnit.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuotientIntegralUnit.lean#L26-L28

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

theorem GlobalTheory.UnitDiscAlg.QuotAlg.comp2 {e₁ e₂ e₃ : R} (h12 : e₁ * e₂ = 0) (h22 : e₂ * e₂ = e₂) (h23 : e₂ * e₃ = 0)
    (α β γ : R) : (α * e₁ + β * e₂ + γ * e₃) * e₂ = β * e₂ := by sorry
