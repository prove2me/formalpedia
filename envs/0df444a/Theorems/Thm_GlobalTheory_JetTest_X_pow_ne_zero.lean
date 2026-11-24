-- Prove2me | Theorems.Thm_GlobalTheory_JetTest_X_pow_ne_zero
-- name    : GlobalTheory.JetTest.X_pow_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:40:46.051618+00:00
-- url     : https://prove2.me/theorems/4a0a3bc7-9891-48d6-b4a9-fec3c8d75757
-- title:
--   Jet Test: X pow ne zero
-- statement:
--   The Jet Test construction uses the X pow ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L21-L27

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

theorem GlobalTheory.JetTest.X_pow_ne_zero [Nontrivial R] (i : ι) :
    (Ideal.Quotient.mk _ (X i ^ m) : Jet R ι m) ≠ 0 := by sorry
