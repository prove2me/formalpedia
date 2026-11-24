-- Prove2me | Theorems.Thm_GlobalTheory_SW_thH_siegel_operator
-- name    : GlobalTheory.SW.thH_siegel_operator
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:46:08.787555+00:00
-- url     : https://prove2.me/theorems/5723e1b4-3b9b-4bb5-9c4d-b4895402d1e8
-- title:
--   SW: th H siegel operator
-- statement:
--   The SW construction uses the th H siegel operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHSiegelOperator.lean#L202-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHSiegelOperator.lean#L202-L269

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperator
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
open scoped ComplexConjugate ComplexOrder Real Classical
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical

theorem GlobalTheory.SW.thH_siegel_operator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Ψ : Finset (E →+* ℂ)), _root_.GlobalTheory.SW.IsType Ψ → ∀ (n N : ℕ)
    (φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ), _root_.GlobalTheory.SW.IsSB φ →
    _root_.GlobalTheory.SW.IsSB (_root_.GlobalTheory.SW.dropF φ) ∧
    ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ (N + 1),
    _root_.GlobalTheory.SW.dropZ Ψ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N ∧
    (∀ t : ℝ, 0 ≤ t → _root_.GlobalTheory.SW.pushZ Ψ Z (Pi.single 0 1) t ∈
      _root_.GlobalTheory.SW.Hn Ψ (N + 1)) ∧
    ∀ z z' : _root_.GlobalTheory.SW.CM Ψ n (N + 1),
    Tendsto (fun t : ℝ => _root_.GlobalTheory.SW.thH Ψ φ (_root_.GlobalTheory.SW.pushZ Ψ Z (Pi.single 0 1) t)
      z z') atTop
      (𝓝 (_root_.GlobalTheory.SW.thH Ψ (_root_.GlobalTheory.SW.dropF φ) (_root_.GlobalTheory.SW.dropZ Ψ Z)
        (fun τ => (z τ).submatrix id Fin.succ) (fun τ => (z' τ).submatrix id Fin.succ))) := by sorry
