-- Prove2me | Theorems.Thm_GlobalTheory_SeriesNakayama_exists_projection
-- name    : GlobalTheory.SeriesNakayama.exists_projection
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:54:25.993816+00:00
-- url     : https://prove2.me/theorems/1a931be7-013a-4c0f-a6e2-f76f2c447e24
-- title:
--   Series Nakayama: exists projection
-- statement:
--   The Series Nakayama construction uses the exists projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SpanModEquationsLift.lean#L44-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SpanModEquationsLift.lean#L44-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SpanModEquationsLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.SeriesNakayama

theorem GlobalTheory.SeriesNakayama.exists_projection {O K : Type*} [CommRing O] [IsLocalRing O] [Field K] (f : O →+* K)
    (hf : RingHom.ker f = IsLocalRing.maximalIdeal O) :
    ∃ (μ : K →+ K) (l : K → O), (∀ a, f (l a) = μ a) ∧ (∀ a o, μ (a * f o) = μ a * f o) ∧
      ∀ o, μ (f o) = f o := by sorry
