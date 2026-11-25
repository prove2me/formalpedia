-- Prove2me | Theorems.Thm_GlobalTheory_JetTest_jetSubstPS_add_C
-- name    : GlobalTheory.JetTest.jetSubstPS_add_C
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:11:50.090834+00:00
-- url     : https://prove2.me/theorems/07e3e132-02c6-4c81-bb06-81fb327c6f12
-- title:
--   Jet Test: jet Subst PS add C
-- statement:
--   The Jet Test construction uses the jet Subst PS add C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L93-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L93-L102

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

theorem GlobalTheory.JetTest.jetSubstPS_add_C {κ : Type} [Fintype κ] [DecidableEq κ] (φ : ι → MvPowerSeries κ R) (c : ι → R) :
    (jetSubstPS (m := m) fun i => φ i + MvPowerSeries.C (c i)) = jetSubstPS (m := m) φ := by sorry
