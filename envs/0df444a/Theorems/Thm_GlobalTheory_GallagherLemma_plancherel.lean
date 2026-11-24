-- Prove2me | Theorems.Thm_GlobalTheory_GallagherLemma_plancherel
-- name    : GlobalTheory.GallagherLemma.plancherel
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:43:16.223809+00:00
-- url     : https://prove2.me/theorems/fc6fc448-8f1e-452a-89fd-8a7cefc8aca6
-- title:
--   Gallagher Lemma: plancherel
-- statement:
--   The Gallagher Lemma construction uses the plancherel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegralNormSqLp.lean#L41-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegralNormSqLp.lean#L41-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped FourierTransform SchwartzMap Real
open GlobalTheory GlobalTheory.GallagherLemma

theorem GlobalTheory.GallagherLemma.plancherel {f : ℝ → ℂ} (hf : Integrable f) (h2 : MemLp f 2) :
    Integrable (fun x => ‖𝓕 f x‖ ^ 2) ∧ ∫ x, ‖𝓕 f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by sorry
