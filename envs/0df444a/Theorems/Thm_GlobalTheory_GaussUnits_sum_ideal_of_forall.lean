-- Prove2me | Theorems.Thm_GlobalTheory_GaussUnits_sum_ideal_of_forall
-- name    : GlobalTheory.GaussUnits.sum_ideal_of_forall
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:54:12.449736+00:00
-- url     : https://prove2.me/theorems/e99bd3cc-3bce-42cf-ba08-5cae23929d14
-- title:
--   Gauss Units: sum ideal of forall
-- statement:
--   The Gauss Units construction uses the sum ideal of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussUnitsNormSq.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussUnitsNormSq.lean#L39-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussUnitsNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ComplexConjugate Finset
open GlobalTheory
open GlobalTheory.GaussUnits
variable {R : Type} [CommRing R] [Fintype R]

theorem GlobalTheory.GaussUnits.sum_ideal_of_forall (I : Ideal R) [DecidablePred (· ∈ I)] (ψ : AddChar R ℂ) (b : R)
    (hb : ∀ x ∈ I, b * x = 0) :
    ∑ x, (if x ∈ I then ψ (b * x) else 0) = ((univ.filter (· ∈ I)).card : ℂ) := by sorry
