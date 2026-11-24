-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBoundTests_exists_half
-- name    : GlobalTheory.LatticeBoundTests.exists_half
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:58:31.339144+00:00
-- url     : https://prove2.me/theorems/01d38e45-dbe9-4328-8714-2f7c7000c078
-- title:
--   Lattice Bound Tests: exists half
-- statement:
--   The Lattice Bound Tests construction uses the exists half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/PremisesInhabited.lean#L91-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/PremisesInhabited.lean#L91-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_PremisesInhabited
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBoundTests
open NumberField

theorem GlobalTheory.LatticeBoundTests.exists_half : ∃ w : 𝓞 K₃, (w : K₃) + IsCMField.complexConj K₃ w = 1 := by sorry
