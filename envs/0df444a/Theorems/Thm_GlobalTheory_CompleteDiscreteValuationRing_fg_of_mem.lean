-- Prove2me | Theorems.Thm_GlobalTheory_CompleteDiscreteValuationRing_fg_of_mem
-- name    : GlobalTheory.CompleteDiscreteValuationRing.fg_of_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:55.191021+00:00
-- url     : https://prove2.me/theorems/03a055d6-1dfb-4a4f-9c7c-4da89f696933
-- title:
--   Complete Discrete Valuation Ring: fg of mem
-- statement:
--   The Complete Discrete Valuation Ring construction uses the fg of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrOfDimOne.lean#L7-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrOfDimOne.lean#L7-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrOfDimOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompleteDiscreteValuationRing

theorem GlobalTheory.CompleteDiscreteValuationRing.fg_of_mem {A B : Type} [CommRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
    [Algebra A B] (a : A) (ha : algebraMap A B a ≠ 0)
    (hart : IsArtinian A (A ⧸ Ideal.span {a}))
    (hden : ∀ x : B, ∃ (n : ℕ) (r : A), algebraMap A B a ^ n * x = algebraMap A B r)
    (J : Ideal B) (hJ : algebraMap A B a ∈ J) : J.FG := by sorry
