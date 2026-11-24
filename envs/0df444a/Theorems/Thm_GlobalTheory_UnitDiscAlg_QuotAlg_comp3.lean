-- Prove2me | Theorems.Thm_GlobalTheory_UnitDiscAlg_QuotAlg_comp3
-- name    : GlobalTheory.UnitDiscAlg.QuotAlg.comp3
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:25:38.620806+00:00
-- url     : https://prove2.me/theorems/e519ccfd-250d-4015-bc69-1f6c860c1c7c
-- title:
--   Quot Alg: comp3
-- statement:
--   The Quot Alg construction uses the comp3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuotientIntegralUnit.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuotientIntegralUnit.lean#L30-L32

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

theorem GlobalTheory.UnitDiscAlg.QuotAlg.comp3 {e₁ e₂ e₃ : R} (h13 : e₁ * e₃ = 0) (h23 : e₂ * e₃ = 0) (h33 : e₃ * e₃ = e₃)
    (α β γ : R) : (α * e₁ + β * e₂ + γ * e₃) * e₃ = γ * e₃ := by sorry
