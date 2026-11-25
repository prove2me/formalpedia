-- Prove2me | Theorems.Thm_GroundTheory_LocalField_cycHerbrand_integerUnits_eq_one
-- name    : GroundTheory.LocalField.cycHerbrand_integerUnits_eq_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:26:49.800808+00:00
-- url     : https://prove2.me/theorems/9eaad7a0-aeae-46e6-8c16-bdf25907caed
-- title:
--   Local Field: cyc Herbrand integer Units eq one
-- statement:
--   The Local Field construction uses the cyc Herbrand integer Units eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocal.lean#L24-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocal.lean#L24-L36

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable [IsGalois K L] {σ : L ≃ₐ[K] L}

theorem GroundTheory.LocalField.cycHerbrand_integerUnits_eq_one (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ = 1 := by sorry
