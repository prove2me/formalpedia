-- Prove2me | Theorems.Thm_GlobalTheory_SW_UniSp_transport
-- name    : GlobalTheory.SW.UniSp.transport
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:44:58.749412+00:00
-- url     : https://prove2.me/theorems/97dd69a3-c4e8-4082-969d-2c9c0429ec62
-- title:
--   Uni Sp: transport
-- statement:
--   The Uni Sp construction uses the transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L17-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L17-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UniSp
noncomputable section
variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]
  {S : Matrix ι K ℂ} {S' : Matrix K ι ℂ}

theorem GlobalTheory.SW.UniSp.transport (h1 : S * S' = 1) (h2 : S' * S = 1) {a b c d T W Qi : Matrix K K ℂ}
    (hQ : (c * T + d) * Qi = 1) (hW : (a * T + b) * Qi = W) {den : Matrix ι ι ℂ}
    (hden : den = S'ᵀ * c * S' * (S * T * Sᵀ) + S'ᵀ * d * Sᵀ) :
    den.det = (c * T + d).det ∧
    (S * a * S' * (S * T * Sᵀ) + S * b * Sᵀ) * den⁻¹ = S * W * Sᵀ ∧
    ∀ w : K → ℂ, (S *ᵥ w) ᵥ* den⁻¹ = S *ᵥ (w ᵥ* Qi) ∧
      (S *ᵥ w) ⬝ᵥ (den⁻¹ * (S'ᵀ * c * S')) *ᵥ (S *ᵥ w) = w ⬝ᵥ (Qi * c) *ᵥ w := by sorry
