-- Prove2me | Theorems.Thm_GlobalTheory_JetTest_jetAug_mk
-- name    : GlobalTheory.JetTest.jetAug_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:13.337832+00:00
-- url     : https://prove2.me/theorems/6f96b226-0133-4ed0-b0e2-b04e7d9721d2
-- title:
--   Jet Test: jet Aug mk
-- statement:
--   The Jet Test construction uses the jet Aug mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L62-L65

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

theorem GlobalTheory.JetTest.jetAug_mk (p : MvPolynomial ι R) :
    (jetAug : Jet R ι m →ₐ[R] R) (Ideal.Quotient.mk _ p) = constantCoeff p := by sorry
