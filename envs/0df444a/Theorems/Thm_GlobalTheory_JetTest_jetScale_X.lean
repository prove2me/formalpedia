-- Prove2me | Theorems.Thm_GlobalTheory_JetTest_jetScale_X
-- name    : GlobalTheory.JetTest.jetScale_X
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:11:33.954591+00:00
-- url     : https://prove2.me/theorems/9dfe5a52-2220-4ebc-bbbd-0eaa7bf99b0f
-- title:
--   Jet Test: jet Scale X
-- statement:
--   The Jet Test construction uses the jet Scale X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L73-L77

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_JetTruncNotInjective
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
open GlobalTheory GlobalTheory.JetTest
open MvPolynomial Formalism.L2.Pj
variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}

theorem GlobalTheory.JetTest.jetScale_X (c : ι → R) (i : ι) :
    (jetScale c : Jet R ι m →ₐ[R] Jet R ι m) (Ideal.Quotient.mk _ (X i)) =
      c i • (Ideal.Quotient.mk _ (X i) : Jet R ι m) := by sorry
