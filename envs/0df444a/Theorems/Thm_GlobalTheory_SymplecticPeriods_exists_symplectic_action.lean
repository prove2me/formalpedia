-- Prove2me | Theorems.Thm_GlobalTheory_SymplecticPeriods_exists_symplectic_action
-- name    : GlobalTheory.SymplecticPeriods.exists_symplectic_action
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:25:19.15565+00:00
-- url     : https://prove2.me/theorems/6a686563-c9c9-4233-b222-dcdfa4e5837c
-- title:
--   Symplectic Periods: exists symplectic action
-- statement:
--   The Symplectic Periods construction uses the exists symplectic action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsSymplecticActionOfPeriodLatticeMap.lean#L44-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsSymplecticActionOfPeriodLatticeMap.lean#L44-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsSymplecticActionOfPeriodLatticeMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SymplecticPeriods
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.SymplecticPeriods.exists_symplectic_action (ι : Type) [Fintype ι] [DecidableEq ι]
    (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ)))
    (hF : ∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) :
    ∃ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ τ ∈ Siegel ι, ∀ τ' M : Matrix ι ι ℂ, τ'.IsSymm →
      (∀ u, M *ᵥ (qv u.1 + τ *ᵥ qv u.2) = qv (F u).1 + τ' *ᵥ qv (F u).2) →
      τ' = spAct σ τ ∧ M = ((spDen σ τ)⁻¹)ᵀ := by sorry
