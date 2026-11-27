-- Prove2me | Theorems.Thm_GlobalTheory_map_maximalIdeal_le_jacobson_of_finite
-- name    : GlobalTheory.map_maximalIdeal_le_jacobson_of_finite
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:03.523154+00:00
-- url     : https://prove2.me/theorems/d07af6fa-0577-5fbb-a0df-7935b0a457fe
-- title:
--   Global Theory: map maximal Ideal le jacobson of finite
-- statement:
--   The Global Theory construction uses the map maximal Ideal le jacobson of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L104-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L104-L109

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

theorem GlobalTheory.map_maximalIdeal_le_jacobson_of_finite (R S : Type*) [CommRing R] [IsLocalRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] :
    (maximalIdeal R).map (algebraMap R S) ≤ (⊥ : Ideal S).jacobson := by sorry
