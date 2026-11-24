-- Prove2me | Theorems.Thm_GlobalTheory_SW_UniSp_local_quad
-- name    : GlobalTheory.SW.UniSp.local_quad
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:45:47.887901+00:00
-- url     : https://prove2.me/theorems/6c607919-4dcd-457a-8e7f-8d7cfd1bc8e5
-- title:
--   Uni Sp: local quad
-- statement:
--   The Uni Sp construction uses the local quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L111-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L111-L126

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
variable {m o : Type} [Fintype m] [Fintype o] [DecidableEq o]
variable [DecidableEq m]

theorem GlobalTheory.SW.UniSp.local_quad {C D Z : Matrix m m ℂ} (h4 : C * Dᴴ = D * Cᴴ) (hP : (Z * Cᴴ + Dᴴ).det ≠ 0)
    (hQ : (C * Z + D).det ≠ 0) (z z' : m → ℂ) :
    Sum.elim z z' ⬝ᵥ (fromBlocks ((Z * Cᴴ + Dᴴ)⁻¹)ᵀ 0 0 (C * Z + D)⁻¹ * (sw m * dl C)) *ᵥ
      Sum.elim z z' = 2 * (z' ⬝ᵥ ((C * Z + D)⁻¹ * C) *ᵥ z) := by sorry
