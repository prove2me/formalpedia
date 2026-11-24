-- Prove2me | Theorems.Thm_GlobalTheory_comap_eq_maximalIdeal_of_finite
-- name    : GlobalTheory.comap_eq_maximalIdeal_of_finite
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:26:58.480961+00:00
-- url     : https://prove2.me/theorems/4fe45b68-51ea-4bab-b103-15d7aceeefe9
-- title:
--   Global Theory: comap eq maximal Ideal of finite
-- statement:
--   The Global Theory construction uses the comap eq maximal Ideal of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L99-L102

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

theorem GlobalTheory.comap_eq_maximalIdeal_of_finite {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S] (n : Ideal S) [n.IsMaximal] :
    n.comap (algebraMap R S) = maximalIdeal R := by sorry
