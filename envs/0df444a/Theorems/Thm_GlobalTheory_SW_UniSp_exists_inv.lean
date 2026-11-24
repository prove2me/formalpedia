-- Prove2me | Theorems.Thm_GlobalTheory_SW_UniSp_exists_inv
-- name    : GlobalTheory.SW.UniSp.exists_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:43.55212+00:00
-- url     : https://prove2.me/theorems/96c32931-850a-4c69-b330-1e0f503062d5
-- title:
--   Uni Sp: exists inv
-- statement:
--   The Uni Sp construction uses the exists inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L164-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L164-L182

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
open Classical
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
variable {Ψ : Finset (E →+* ℂ)} {N : ℕ}

theorem GlobalTheory.SW.UniSp.exists_inv (hΨ : IsType Ψ) : ∃ S' : Matrix ((Fin N ⊕ Fin N) × Ψ) (QI E N) ℂ,
    Sm Ψ N * S' = 1 ∧ S' * Sm Ψ N = 1 := by sorry
