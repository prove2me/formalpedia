-- Prove2me | Theorems.Thm_GlobalTheory_CapelliNegT_glRel_negT_and_qdet
-- name    : GlobalTheory.CapelliNegT.glRel_negT_and_qdet
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:46.076789+00:00
-- url     : https://prove2.me/theorems/1d327c5a-953c-45e4-bc01-6c423d9411a7
-- title:
--   Capelli Neg T: gl Rel neg T and qdet
-- statement:
--   The Capelli Neg T construction uses the gl Rel neg T and qdet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GlRelNegTAndQdet.lean#L11-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GlRelNegTAndQdet.lean#L11-L52

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmRowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GlRelNegTAndQdet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory GlobalTheory.CapelliNegT
open Finset

theorem GlobalTheory.CapelliNegT.glRel_negT_and_qdet :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), _root_.Formalism.REAL.GlRel E →
      _root_.Formalism.REAL.GlRel (fun a b => -E b a) ∧
        ∀ u : ℂ, _root_.Formalism.REAL.qdet (fun a b => -E b a) u = ((-1 : ℂ) ^ n) • _root_.Formalism.REAL.qdet E ((n : ℂ) - 1 - u) := by sorry
