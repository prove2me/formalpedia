-- Prove2me | Theorems.Thm_GlobalTheory_SW_UniSp_transport_sp
-- name    : GlobalTheory.SW.UniSp.transport_sp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:45:01.994565+00:00
-- url     : https://prove2.me/theorems/fc3e2686-bfdd-4e4e-8cb5-5aefd5c39423
-- title:
--   Uni Sp: transport sp
-- statement:
--   The Uni Sp construction uses the transport sp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L46-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L46-L63

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

theorem GlobalTheory.SW.UniSp.transport_sp (h1 : S * S' = 1) (h2 : S' * S = 1) {a b c d : Matrix K K ℂ}
    (e1 : b * aᵀ = a * bᵀ) (e2 : a * dᵀ = b * cᵀ + 1) (e3 : d * aᵀ = c * bᵀ + 1)
    (e4 : d * cᵀ = c * dᵀ) :
    fromBlocks (S * a * S') (S * b * Sᵀ) (S'ᵀ * c * S') (S'ᵀ * d * Sᵀ) * Matrix.J ι ℂ *
      (fromBlocks (S * a * S') (S * b * Sᵀ) (S'ᵀ * c * S') (S'ᵀ * d * Sᵀ))ᵀ = Matrix.J ι ℂ := by sorry
