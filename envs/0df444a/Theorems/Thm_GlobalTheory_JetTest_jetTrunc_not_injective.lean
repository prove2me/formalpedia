-- Prove2me | Theorems.Thm_GlobalTheory_JetTest_jetTrunc_not_injective
-- name    : GlobalTheory.JetTest.jetTrunc_not_injective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:11:31.090739+00:00
-- url     : https://prove2.me/theorems/8d3108ec-e0a5-5cff-afcf-193d0983c976
-- title:
--   Jet Test: jet Trunc not injective
-- statement:
--   The Jet Test construction uses the jet Trunc not injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L85-L91

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

theorem GlobalTheory.JetTest.jetTrunc_not_injective [Nontrivial R] (i : ι) :
    ¬ Function.Injective (jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m) := by sorry
