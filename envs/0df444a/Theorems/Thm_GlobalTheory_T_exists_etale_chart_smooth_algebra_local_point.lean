-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_etale_chart_smooth_algebra_local_point
-- name    : GlobalTheory.T.exists_etale_chart_smooth_algebra_local_point
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:29:01.154783+00:00
-- url     : https://prove2.me/theorems/54fb1884-e443-492b-beaa-600a05301bff
-- title:
--   T: exists etale chart smooth algebra local point
-- statement:
--   The T construction uses the exists etale chart smooth algebra local point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEtaleChartSmoothAlgebraLocalPointStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEtaleChartSmoothAlgebraLocalPointStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEtaleChartSmoothAlgebraLocalPoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEtaleChartSmoothAlgebraLocalPointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_etale_chart_smooth_algebra_local_point : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R), ∃ (g : ℕ) (t : Fin g → A) (h : A), (∀ i, ε (t i) = 0) ∧ IsUnit (ε h) ∧ GlobalTheory.DenseSec.EtChart R A t h := by sorry
