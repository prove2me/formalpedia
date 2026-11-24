-- Prove2me | Theorems.Thm_GlobalTheory_LatticeMean_exists_strict_domain
-- name    : GlobalTheory.LatticeMean.exists_strict_domain
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:00:39.808087+00:00
-- url     : https://prove2.me/theorems/08bfe073-7842-4a7c-b447-587628706981
-- title:
--   Lattice Mean: exists strict domain
-- statement:
--   The Lattice Mean construction uses the exists strict domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SetAverageProdFundamentalDomainPlaneLatticePow.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SetAverageProdFundamentalDomainPlaneLatticePow.lean#L8-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SetAverageProdFundamentalDomainPlaneLatticePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
open GlobalTheory GlobalTheory.LatticeMean

theorem GlobalTheory.LatticeMean.exists_strict_domain (Λ : AddSubgroup ℂ)
    (h : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    Countable Λ ∧ ∃ F : Set ℂ, MeasurableSet F ∧ ∀ x : ℂ, ∃! g : Λ, (g : ℂ) + x ∈ F := by sorry
