-- Prove2me | Theorems.Thm_GlobalTheory_henselianRing_of_finite
-- name    : GlobalTheory.henselianRing_of_finite
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:02.494498+00:00
-- url     : https://prove2.me/theorems/5a8ccc1a-dd00-4f4f-9a51-e3d626d9b172
-- title:
--   Global Theory: henselian Ring of finite
-- statement:
--   The Global Theory construction uses the henselian Ring of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L219-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L219-L316

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct

theorem GlobalTheory.henselianRing_of_finite (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] (J : Ideal S)
    (hJ : J ≤ (⊥ : Ideal S).jacobson) : HenselianRing S J := by sorry
