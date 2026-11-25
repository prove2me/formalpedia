-- Prove2me | Theorems.Thm_GlobalTheory_JetTest_jetTrunc_surjective
-- name    : GlobalTheory.JetTest.jetTrunc_surjective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:11:36.955474+00:00
-- url     : https://prove2.me/theorems/6db0de51-c532-47b8-8439-eb8c0f19879b
-- title:
--   Jet Test: jet Trunc surjective
-- statement:
--   The Jet Test construction uses the jet Trunc surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L79-L83

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

theorem GlobalTheory.JetTest.jetTrunc_surjective :
    Function.Surjective (jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m) := by sorry
