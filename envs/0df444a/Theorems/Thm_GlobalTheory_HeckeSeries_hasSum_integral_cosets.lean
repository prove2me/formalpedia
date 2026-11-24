-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSeries_hasSum_integral_cosets
-- name    : GlobalTheory.HeckeSeries.hasSum_integral_cosets
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:27.275272+00:00
-- url     : https://prove2.me/theorems/f9d002ec-d34f-45fb-822c-aba8f3048151
-- title:
--   Hecke Series: has Sum integral cosets
-- statement:
--   The Hecke Series construction uses the has Sum integral cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumHeckeSeriesBorelSphericalIntegralCosets.lean#L169-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumHeckeSeriesBorelSphericalIntegralCosets.lean#L169-L245

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesBorelSphericalIntegralCosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.HeckeSeries
open MeasureTheory ValuativeRel

theorem GlobalTheory.HeckeSeries.hasSum_integral_cosets : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ)
    (φ : GL (Fin n) k → ℂ), _root_.GlobalTheory.SatakeBound.IsBorelSph k γ φ → ∀ X : ℂ,
    (∀ i : Fin n, ‖(_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1) →
    HasSum (fun c : {c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n) //
        (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} =>
      X ^ (_root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ c.1.out)
      (∏ i : Fin n, (1 - (_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) := by sorry
