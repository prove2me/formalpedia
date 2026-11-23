-- Prove2me | Theorems.Thm_GlobalTheory_JetTest_jetMap_mk
-- name    : GlobalTheory.JetTest.jetMap_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:34.017899+00:00
-- url     : https://prove2.me/theorems/a391e2e5-786f-441d-aa1b-79f4fd8f0e01
-- title:
--   Jet Test: jet Map mk
-- statement:
--   The Jet Test construction uses the jet Map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L59-L60

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

theorem GlobalTheory.JetTest.jetMap_mk {κ : Type} (φ : ι → MvPolynomial κ R) (hφ : ∀ i, φ i ∈ orig R κ) (p : MvPolynomial ι R) :
    (jetMap (m := m) φ hφ) (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (aeval φ p) := by sorry
