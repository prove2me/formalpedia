-- Prove2me | Theorems.Thm_GlobalTheory_JetTest_jetTan_X
-- name    : GlobalTheory.JetTest.jetTan_X
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:11:31.570187+00:00
-- url     : https://prove2.me/theorems/a298ae79-3a3e-55ef-a910-6af9050953a9
-- title:
--   Jet Test: jet Tan X
-- statement:
--   The Jet Test construction uses the jet Tan X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L67-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L67-L71

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

theorem GlobalTheory.JetTest.jetTan_X [DecidableEq ι] (l i : ι) :
    (jetTan l : Jet R ι (m + 1) →ₐ[R] DualNumber R) (Ideal.Quotient.mk _ (X i)) =
      if i = l then DualNumber.eps else 0 := by sorry
