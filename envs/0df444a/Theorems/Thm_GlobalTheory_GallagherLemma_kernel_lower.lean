-- Prove2me | Theorems.Thm_GlobalTheory_GallagherLemma_kernel_lower
-- name    : GlobalTheory.GallagherLemma.kernel_lower
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:43:09.922331+00:00
-- url     : https://prove2.me/theorems/92aba655-6502-42e2-8615-c57e206f61bb
-- title:
--   Gallagher Lemma: kernel lower
-- statement:
--   The Gallagher Lemma construction uses the kernel lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegralNormSqLp.lean#L80-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegralNormSqLp.lean#L80-L97

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

theorem GlobalTheory.GallagherLemma.kernel_lower (δ s : ℝ) (hδ : 0 ≤ δ) (hs : |s| * δ ≤ 1) :
    δ / 2 ≤ ‖∫ u in (0 : ℝ)..δ, cexp ((s * u : ℝ) * I)‖ := by sorry
