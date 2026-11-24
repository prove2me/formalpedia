-- Prove2me | Theorems.Thm_GlobalTheory_HeckeMellin_hasSum_integral_theta
-- name    : GlobalTheory.HeckeMellin.hasSum_integral_theta
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:45.631031+00:00
-- url     : https://prove2.me/theorems/eaffa073-ae15-4cd8-8e73-e265844c1d69
-- title:
--   Hecke Mellin: has Sum integral theta
-- statement:
--   The Hecke Mellin construction uses the has Sum integral theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumIntegralThetaMellinInterchange.lean#L13-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumIntegralThetaMellinInterchange.lean#L13-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIntegralThetaMellinInterchange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory
open GlobalTheory GlobalTheory.HeckeMellin

theorem GlobalTheory.HeckeMellin.hasSum_integral_theta (I : Type) [Fintype I] (ι : Type) [Countable ι] (e : ι → I → ℂ) (a : ι → ℂ) (C : ℝ)
    (hC : ∀ j, ‖a j‖ ≤ C) (n : I → ℤ) (s : ℂ) (p : (I → ℝ) → ℝ) (hp : Measurable p) (hp0 : ∀ y, 0 ≤ p y)
    (hp1 : ∀ y, p y ≤ 1) (hint : ∀ j, Integrable (GlobalTheory.HeckeMellin.term n s (e j)))
    (hsum : Summable (fun j => ∫ y, p y * ‖GlobalTheory.HeckeMellin.term n s (e j) y‖)) :
    HasSum (fun j => a j * ∫ y, (p y : ℂ) * GlobalTheory.HeckeMellin.term n s (e j) y)
      (∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) := by sorry
