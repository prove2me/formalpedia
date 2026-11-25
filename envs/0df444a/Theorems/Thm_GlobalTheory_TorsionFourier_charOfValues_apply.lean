-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFourier_charOfValues_apply
-- name    : GlobalTheory.TorsionFourier.charOfValues_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:40.983074+00:00
-- url     : https://prove2.me/theorems/bbfdb3c4-9127-4e38-b723-7039ed685ab5
-- title:
--   Torsion Fourier: char Of Values apply
-- statement:
--   The Torsion Fourier construction uses the char Of Values apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FourierExtractionTsumClass.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FourierExtractionTsumClass.lean#L43-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open GlobalTheory.TorsionFourier
variable {K X : Type} [Field K] [AddCommGroup X]

theorem GlobalTheory.TorsionFourier.charOfValues_apply {ι : Type} [Fintype ι] (b : Basis ι ℤ X) (u : ι → Kˣ) (x : X) :
    charOfValues b u (Multiplicative.ofAdd x) = ∏ i, u i ^ (b.repr x i) := by sorry
