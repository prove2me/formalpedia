-- Prove2me | Theorems.Thm_GlobalTheory_SW_TransComp_key
-- name    : GlobalTheory.SW.TransComp.key
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:19.470797+00:00
-- url     : https://prove2.me/theorems/ac7145bf-e7f4-42ab-8f0e-42c983507216
-- title:
--   Trans Comp: key
-- statement:
--   The Trans Comp construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationLawMul.lean#L52-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationLawMul.lean#L52-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMul
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TransComp
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.SW.TransComp.key {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (h : σ ∈ Matrix.symplecticGroup ι ℚ)
    {τ : Matrix ι ι ℂ} (hτ : τ.IsSymm) (hd : (spDen σ τ).det ≠ 0) (hs : (spAct σ τ).IsSymm) :
    qm σ.toBlocks₁₁ = spAct σ τ * qm σ.toBlocks₂₁ + ((spDen σ τ)⁻¹)ᵀ := by sorry
