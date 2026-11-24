-- Prove2me | Theorems.Thm_GlobalTheory_SW_exists_weil_mul
-- name    : GlobalTheory.SW.exists_weil_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:45:18.35856+00:00
-- url     : https://prove2.me/theorems/39fb1c58-3bc7-45fc-b0d7-1efb54effca1
-- title:
--   SW: exists weil mul
-- statement:
--   The SW construction uses the exists weil mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsWeilOfSymplectic.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsWeilOfSymplectic.lean#L13-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandarStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticEqParabolicJParabolicJParabolicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsWeilOfSymplectic
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
open GlobalTheory GlobalTheory.SW

theorem GlobalTheory.SW.exists_weil_mul {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hσ' : σ' ∈ Matrix.symplecticGroup ι ℚ)
    (h : ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧
      TransS σ φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ')
    (h' : ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧
      TransS σ' φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ') :
    ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧
      TransS (σ * σ') φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by sorry
