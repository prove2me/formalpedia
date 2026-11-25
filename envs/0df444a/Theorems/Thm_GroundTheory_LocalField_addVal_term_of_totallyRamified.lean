-- Prove2me | Theorems.Thm_GroundTheory_LocalField_addVal_term_of_totallyRamified
-- name    : GroundTheory.LocalField.addVal_term_of_totallyRamified
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:14:06.328504+00:00
-- url     : https://prove2.me/theorems/07cb5c9f-641b-4c6a-9434-3e0d7c5972ff
-- title:
--   Local Field: add Val term of totally Ramified
-- statement:
--   The Local Field construction uses the add Val term of totally Ramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L382-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L382-L395

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  (h : ramificationIndex K L = Module.finrank K L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include h hϖ

theorem GroundTheory.LocalField.addVal_term_of_totallyRamified (g : 𝒪[K][X]) (i : ℕ) :
    (∀ k, g.coeff i ∈ IsLocalRing.maximalIdeal 𝒪[K] ^ k →
      ((Module.finrank K L * k + i : ℕ) : ℕ∞) ≤
        addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i)) ∧
    (IsUnit (g.coeff i) → addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i) = i) := by sorry
