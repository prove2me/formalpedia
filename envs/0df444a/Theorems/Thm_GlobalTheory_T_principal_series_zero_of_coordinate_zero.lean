-- Prove2me | Theorems.Thm_GlobalTheory_T_principal_series_zero_of_coordinate_zero
-- name    : GlobalTheory.T.principal_series_zero_of_coordinate_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:55:18.136187+00:00
-- url     : https://prove2.me/theorems/72b6f331-2e98-4089-bfc1-80fcec24b8f7
-- title:
--   T: principal series zero of coordinate zero
-- statement:
--   The T construction uses the principal series zero of coordinate zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrincipalSeriesZeroOfCoordinateZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrincipalSeriesZeroOfCoordinateZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesZeroOfCoordinateZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesZeroOfCoordinateZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.principal_series_zero_of_coordinate_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), GlobalTheory.PrinTwo.ev f 1 = 0 → (∀ x : k, GlobalTheory.PrinTwo.coord f x = 0) → f = 0 := by sorry
