-- Prove2me | Theorems.Thm_GlobalTheory_HeckeDual_hasSum_dual
-- name    : GlobalTheory.HeckeDual.hasSum_dual
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:03:35.862966+00:00
-- url     : https://prove2.me/theorems/8d828030-012a-4b84-b7c4-f3ea0b0eaf60
-- title:
--   Hecke Dual: has Sum dual
-- statement:
--   The Hecke Dual construction uses the has Sum dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumHeckeSeriesSphericalIntegralInverse.lean#L105-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumHeckeSeriesSphericalIntegralInverse.lean#L105-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesBorelSphericalIntegralCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverse
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
open GlobalTheory GlobalTheory.HeckeDual
open GlobalTheory.SatakeFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
open MeasureTheory ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ}

theorem GlobalTheory.HeckeDual.hasSum_dual : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ)
    (φ : GL (Fin n) k → ℂ), _root_.GlobalTheory.SatakeBound.IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ,
    (∀ i : Fin n, ‖(_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1) →
    HasSum (fun c : {c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n) //
        (∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k])} =>
      X ^ (-_root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat *
        φ c.1.out)
      (∏ i : Fin n, (1 - (_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) := by sorry
