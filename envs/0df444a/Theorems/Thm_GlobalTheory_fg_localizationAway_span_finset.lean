-- Prove2me | Theorems.Thm_GlobalTheory_fg_localizationAway_span_finset
-- name    : GlobalTheory.fg_localizationAway_span_finset
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:35.246842+00:00
-- url     : https://prove2.me/theorems/221ac1ef-a2c6-4bbc-8b56-c6f24eb1b9d4
-- title:
--   Global Theory: fg localization Away span finset
-- statement:
--   The Global Theory construction uses the fg localization Away span finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FgLocalizationAwaySpanFinset.lean#L7-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FgLocalizationAwaySpanFinset.lean#L7-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FgLocalizationAwaySpanFinset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Submodule

theorem GlobalTheory.fg_localizationAway_span_finset
    {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A']
    [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R)
    [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A']
    (N : Submodule R' A') (hN : N.FG) :
    ∃ E : Finset A, ∀ b : A, algebraMap A A' b ∈ N →
      ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A) := by sorry
