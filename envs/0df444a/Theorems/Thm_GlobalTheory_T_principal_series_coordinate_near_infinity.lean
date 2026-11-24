-- Prove2me | Theorems.Thm_GlobalTheory_T_principal_series_coordinate_near_infinity
-- name    : GlobalTheory.T.principal_series_coordinate_near_infinity
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:55:59.347262+00:00
-- url     : https://prove2.me/theorems/53c698c5-dd81-41c2-8120-cda559183262
-- title:
--   T: principal series coordinate near infinity
-- statement:
--   The T construction uses the principal series coordinate near infinity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrincipalSeriesCoordinateNearInfinityStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrincipalSeriesCoordinateNearInfinityStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesCoordinateNearInfinity
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesCoordinateNearInfinityStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.principal_series_coordinate_near_infinity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ, ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) → GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1 := by sorry
