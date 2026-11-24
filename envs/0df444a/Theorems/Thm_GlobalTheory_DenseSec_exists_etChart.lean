-- Prove2me | Theorems.Thm_GlobalTheory_DenseSec_exists_etChart
-- name    : GlobalTheory.DenseSec.exists_etChart
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:43:44.126898+00:00
-- url     : https://prove2.me/theorems/bcac87cc-8fda-4377-a176-e1403f969d65
-- title:
--   Dense Sec: exists et Chart
-- statement:
--   The Dense Sec construction uses the exists et Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEtaleChartSmoothAlgebraLocalPoint.lean#L28-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEtaleChartSmoothAlgebraLocalPoint.lean#L28-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEtaleChartSmoothAlgebraLocalPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
noncomputable section
open GlobalTheory GlobalTheory.DenseSec
open KaehlerDifferential
open scoped TensorProduct

theorem GlobalTheory.DenseSec.exists_etChart : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] (ε : A →ₐ[R] R), ∃ (g : ℕ) (t : Fin g → A) (h : A),
      (∀ i, ε (t i) = 0) ∧ IsUnit (ε h) ∧ GlobalTheory.DenseSec.EtChart R A t h := by sorry
