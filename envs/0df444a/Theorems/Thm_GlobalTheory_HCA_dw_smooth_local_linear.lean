-- Prove2me | Theorems.Thm_GlobalTheory_HCA_dw_smooth_local_linear
-- name    : GlobalTheory.HCA.dw_smooth_local_linear
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:59:17.092726+00:00
-- url     : https://prove2.me/theorems/d27a2b4e-4616-4df2-a9ab-dc077ed60743
-- title:
--   HCA: dw smooth local linear
-- statement:
--   The HCA construction uses the dw smooth local linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DwSmoothLocalLinear.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DwSmoothLocalLinear.lean#L63-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA

theorem GlobalTheory.HCA.dw_smooth_local_linear : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d)),
    (∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ (dw w u) U) ∧
    (∀ u v : E d → ℂ, Set.EqOn u v U → Set.EqOn (dw w u) (dw w v) U) ∧
    (∀ u v : E d → ℂ, ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U → ∀ s t : ℂ,
      Set.EqOn (dw w (s • u + t • v)) (s • dw w u + t • dw w v) U) := by sorry
