-- Prove2me | Theorems.Thm_GlobalTheory_SW_HeisH_heisH_apply
-- name    : GlobalTheory.SW.HeisH.heisH_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:56.015937+00:00
-- url     : https://prove2.me/theorems/b9f19e50-ba79-4ff2-9465-ab4c21b9dfb8
-- title:
--   Heis H: heis H apply
-- statement:
--   The Heis H construction uses the heis H apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianHeisenbergOperatorLaws.lean#L144-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianHeisenbergOperatorLaws.lean#L144-L153

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

theorem GlobalTheory.SW.HeisH.heisH_apply (d b : Matrix (Fin n) (Fin N) E) (φ : Matrix (Fin n) (Fin N) E → ℂ)
    (x : Matrix (Fin n) (Fin N) E) :
    heisH d b φ x = φ (x - d) * cexp (π * I * (2 * (pairT b x : ℂ) - pairT b d)) := by sorry
