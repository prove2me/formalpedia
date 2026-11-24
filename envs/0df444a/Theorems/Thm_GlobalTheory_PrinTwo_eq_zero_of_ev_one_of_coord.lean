-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_eq_zero_of_ev_one_of_coord
-- name    : GlobalTheory.PrinTwo.eq_zero_of_ev_one_of_coord
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:55:29.969846+00:00
-- url     : https://prove2.me/theorems/6992655b-702d-426a-86c0-d825df1f951b
-- title:
--   Prin Two: eq zero of ev one of coord
-- statement:
--   The Prin Two construction uses the eq zero of ev one of coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrincipalSeriesZeroOfCoordinateZero.lean#L10-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrincipalSeriesZeroOfCoordinateZero.lean#L10-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesZeroOfCoordinateZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.PrinTwo

theorem GlobalTheory.PrinTwo.eq_zero_of_ev_one_of_coord {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : PSp μ₁ μ₂) (h1 : ev f 1 = 0)
    (hc : ∀ x : k, coord f x = 0) : f = 0 := by sorry
