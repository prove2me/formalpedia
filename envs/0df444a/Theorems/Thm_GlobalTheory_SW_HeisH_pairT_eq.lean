-- Prove2me | Theorems.Thm_GlobalTheory_SW_HeisH_pairT_eq
-- name    : GlobalTheory.SW.HeisH.pairT_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:55.330501+00:00
-- url     : https://prove2.me/theorems/e2d85044-cacb-4597-bfa5-d496f7729f00
-- title:
--   Heis H: pair T eq
-- statement:
--   The Heis H construction uses the pair T eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianHeisenbergOperatorLaws.lean#L134-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianHeisenbergOperatorLaws.lean#L134-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeisH
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

theorem GlobalTheory.SW.HeisH.pairT_eq (hΨ : IsType Ψ) (b x : Matrix (Fin n) (Fin N) E) :
    ((pairT b x : ℚ) : ℂ) = ∑ τ : Ψ, ((b.map τ.1 * (x.map τ.1)ᴴ).trace +
      (x.map τ.1 * (b.map τ.1)ᴴ).trace) := by sorry
