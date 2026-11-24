-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_span_pow_eq_top_of_separable
-- name    : GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:38:37.451407+00:00
-- url     : https://prove2.me/theorems/0e68febd-10c5-4597-962d-aaa03d7f4e64
-- title:
--   Unr: span pow eq top of separable
-- statement:
--   The Unr construction uses the span pow eq top of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpanPowGeneratorEqTopOfCharpolySeparable.lean#L11-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpanPowGeneratorEqTopOfCharpolySeparable.lean#L11-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpanPowGeneratorEqTopOfCharpolySeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial

theorem GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable (K : UQ) (B : InvAlg K) (hs : B.P.Separable) :
    Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) = ⊤ := by sorry
