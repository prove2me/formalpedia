-- Prove2me | Theorems.Thm_GlobalTheory_QFam_isIntegral_of_esymm_mem
-- name    : GlobalTheory.QFam.isIntegral_of_esymm_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:59:36.979452+00:00
-- url     : https://prove2.me/theorems/7621b49b-7171-4716-8a82-76cecefc60ac
-- title:
--   QFam: is Integral of esymm mem
-- statement:
--   The QFam construction uses the is Integral of esymm mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralOfEsymmMemSubring.lean#L9-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralOfEsymmMemSubring.lean#L9-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfEsymmMemSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open Polynomial
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.isIntegral_of_esymm_mem (ι : Type) [Fintype ι] (R : Subring ℂ) (x : ι → ℂ)
    (h : ∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, x i) ∈ R) (i : ι) :
    IsIntegral R (x i) := by sorry
