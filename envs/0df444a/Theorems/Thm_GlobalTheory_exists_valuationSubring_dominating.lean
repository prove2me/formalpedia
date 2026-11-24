-- Prove2me | Theorems.Thm_GlobalTheory_exists_valuationSubring_dominating
-- name    : GlobalTheory.exists_valuationSubring_dominating
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:45:48.38726+00:00
-- url     : https://prove2.me/theorems/58a2b4fa-c60e-4239-a099-232cb50a6990
-- title:
--   Global Theory: exists valuation Subring dominating
-- statement:
--   The Global Theory construction uses the exists valuation Subring dominating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringDominatingSubring.lean#L162-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringDominatingSubring.lean#L162-L169

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
noncomputable section
open GlobalTheory
variable {V K K' : Type*} [CommRing V] [Field K] [Field K']

theorem GlobalTheory.exists_valuationSubring_dominating [IsDomain V] [ValuationRing V] [Algebra V K]
    [IsFractionRing V K] (χ : K →+* K') :
    ∃ (V' : ValuationSubring K') (ψ : V →+* V'), IsLocalHom ψ ∧
      (∀ a, (ψ a : K') = χ (algebraMap V K a)) ∧
      ∀ x : K, χ x ∈ V' ↔ x ∈ (algebraMap V K).range := by sorry
