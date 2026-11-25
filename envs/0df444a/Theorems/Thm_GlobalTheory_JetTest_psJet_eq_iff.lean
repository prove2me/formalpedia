-- Prove2me | Theorems.Thm_GlobalTheory_JetTest_psJet_eq_iff
-- name    : GlobalTheory.JetTest.psJet_eq_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:11:55.810164+00:00
-- url     : https://prove2.me/theorems/c457f5fd-9ae9-40f2-8610-3faf61f9d967
-- title:
--   Jet Test: ps Jet eq iff
-- statement:
--   The Jet Test construction uses the ps Jet eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/JetTruncNotInjective.lean#L52-L57

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

theorem GlobalTheory.JetTest.psJet_eq_iff [Fintype ι] [DecidableEq ι] (f g : MvPowerSeries ι R) :
    psJet m f = psJet m g ↔
      ∀ e : ι →₀ ℕ, e.degree ≤ m → MvPowerSeries.coeff e f = MvPowerSeries.coeff e g := by sorry
