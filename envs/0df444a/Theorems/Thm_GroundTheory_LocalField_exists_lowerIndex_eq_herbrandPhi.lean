-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_lowerIndex_eq_herbrandPhi
-- name    : GroundTheory.LocalField.exists_lowerIndex_eq_herbrandPhi
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:51:13.497499+00:00
-- url     : https://prove2.me/theorems/341bfe11-1792-56f5-a850-dabce9ac18d5
-- title:
--   Local Field: exists lower Index eq herbrand Phi
-- statement:
--   The Local Field construction uses the exists lower Index eq herbrand Phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L75-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L75-L120

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
import Definitions.Def_GroundTheory_LocalFields_UpperNumbering
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
open ValuativeRel
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable [IsGalois K L] (M : IntermediateField K L) [IsGalois K M]

theorem GroundTheory.LocalField.exists_lowerIndex_eq_herbrandPhi (σ : L ≃ₐ[K] L) :
    ∃ σ₀ : L ≃ₐ[K] L,
      AlgEquiv.restrictNormalHom M σ₀ = AlgEquiv.restrictNormalHom M σ ∧
      (∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) ≤ lowerIndex K L σ₀) ∧
      (∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ₀ * τ.restrictScalars K) =
        min (lowerIndex M L τ) (lowerIndex K L σ₀)) ∧
      (AlgEquiv.restrictNormalHom M σ = 1 → lowerIndex K L σ₀ = ⊤) ∧
      (AlgEquiv.restrictNormalHom M σ ≠ 1 → ∃ m k : ℕ, lowerIndex K L σ₀ = m ∧
        lowerIndex K M (AlgEquiv.restrictNormalHom M σ) = k ∧
        (k : ℝ) = herbrandPhi M L ((m : ℝ) - 1) + 1) := by sorry
