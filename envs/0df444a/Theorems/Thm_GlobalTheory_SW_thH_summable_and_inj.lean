-- Prove2me | Theorems.Thm_GlobalTheory_SW_thH_summable_and_inj
-- name    : GlobalTheory.SW.thH_summable_and_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:52.881743+00:00
-- url     : https://prove2.me/theorems/65e33b01-7e71-4940-a152-95dc8a709822
-- title:
--   SW: th H summable and inj
-- statement:
--   The SW construction uses the th H summable and inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianThetaSummableAndDeterminesTestFn.lean#L12-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianThetaSummableAndDeterminesTestFn.lean#L12-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
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
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real

theorem GlobalTheory.SW.thH_summable_and_inj : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (Ψ : Finset (E →+* ℂ)), _root_.GlobalTheory.SW.IsType Ψ → ∀ (n N : ℕ)
    (φ : Matrix (Fin n) (Fin N) E → ℂ), _root_.GlobalTheory.SW.IsSB φ →
    ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N,
      (∀ z z', Summable fun x => ‖φ x * cexp (2 * π * I * _root_.GlobalTheory.SW.expo Ψ x Z z z')‖) ∧
      ∀ ψ, _root_.GlobalTheory.SW.IsSB ψ →
        (∀ z z', _root_.GlobalTheory.SW.thH Ψ φ Z z z' = _root_.GlobalTheory.SW.thH Ψ ψ Z z z') → φ = ψ := by sorry
