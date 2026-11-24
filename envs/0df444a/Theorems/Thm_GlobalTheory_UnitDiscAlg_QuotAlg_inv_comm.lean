-- Prove2me | Theorems.Thm_GlobalTheory_UnitDiscAlg_QuotAlg_inv_comm
-- name    : GlobalTheory.UnitDiscAlg.QuotAlg.inv_comm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:26:53.59662+00:00
-- url     : https://prove2.me/theorems/eeeb62b2-4e66-49b3-8850-5195d7e4fa3a
-- title:
--   Quot Alg: inv comm
-- statement:
--   The Quot Alg construction uses the inv comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuotientIntegralUnit.lean#L139-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuotientIntegralUnit.lean#L139-L145

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

theorem GlobalTheory.UnitDiscAlg.QuotAlg.inv_comm {E : Type} [Field E] {n : ℕ} {x N : Matrix (Fin n) (Fin n) E}
    (h : x * N = N * x) : x⁻¹ * N = N * x⁻¹ := by sorry
