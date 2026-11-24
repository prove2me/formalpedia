-- Prove2me | Theorems.Thm_GlobalTheory_SW_UniSp_exists_reg
-- name    : GlobalTheory.SW.UniSp.exists_reg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:45:55.494316+00:00
-- url     : https://prove2.me/theorems/cf65ff64-072d-4754-a516-06a4ba3ba751
-- title:
--   Uni Sp: exists reg
-- statement:
--   The Uni Sp construction uses the exists reg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L201-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L201-L218

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

theorem GlobalTheory.SW.UniSp.exists_reg (X : Matrix (Fin N) (Fin N) E) : ∃ R : Matrix (QI E N) (QI E N) ℚ,
    qm R * Sm Ψ N = Sm Ψ N * blockDiagonal fun τ : Ψ => dl (X.map τ.1) := by sorry
