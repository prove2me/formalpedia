-- Prove2me | Theorems.Thm_GlobalTheory_SW_UniSp_exists_gram
-- name    : GlobalTheory.SW.UniSp.exists_gram
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:44:09.143591+00:00
-- url     : https://prove2.me/theorems/fba36fee-6201-4bd0-af59-c75bb7b3ac5d
-- title:
--   Uni Sp: exists gram
-- statement:
--   The Uni Sp construction uses the exists gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L220-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L220-L238

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

theorem GlobalTheory.SW.UniSp.exists_gram [IsCMField E] (hΨ : IsType Ψ) : ∃ G : Matrix (QI E N) (QI E N) ℚ,
    qm G = Sm Ψ N * blockDiagonal (fun _ : Ψ => sw (Fin N)) * (Sm Ψ N)ᵀ := by sorry
