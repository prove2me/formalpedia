-- Prove2me | Theorems.Thm_GlobalTheory_CollapseCompare_exists_reduction
-- name    : GlobalTheory.CollapseCompare.exists_reduction
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:22:46.714742+00:00
-- url     : https://prove2.me/theorems/6f6fc320-ca77-48be-847a-4b014a45aa88
-- title:
--   Collapse Compare: exists reduction
-- statement:
--   The Collapse Compare construction uses the exists reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CoreIffCollapsesWith.lean#L497-L539
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CoreIffCollapsesWith.lean#L497-L539

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_FlatOmegaSeries
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulFrameMulFrameInvApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CoreIffCollapsesWith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CollapseCompare
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical (frame)
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.CollapseCompare.exists_reduction (β : kˣ) (ν ν₀ : Measure k) [ν.IsAddHaarMeasure] [ν₀.IsAddHaarMeasure]
    (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (J : Subgroup (GL (n ⊕ Fin c) k)) (lam : J →* ℂˣ)
    (bas : GL (n ⊕ Fin c) k) {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Φ ∈ SB _)
    (h1 : HasTargetType μ J lam Φ) (h2 : OneCoset ψ ν μ Φ J) :
    ∃ (t : GL (n ⊕ Fin c) k) (r : ℝ≥0), ∃ Φ₀ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), Adapted t ∧ r ≠ 0 ∧
      HasTargetType μ (cjJ t J) (cjLam t lam) Φ₀ ∧ OneCoset (ψ.mulShift (β : k)) ν₀ μ Φ₀ (cjJ t J) ∧
      (∀ m : Measure (GL n k), IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν₀ (t⁻¹ * bas) m = r⁻¹ • IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν bas m) ∧
      ∀ (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)) (κ : ℝ),
        Core ν₀ (r⁻¹ • μX) (μG.map (cjG t).symm) (cjJ t J) (t⁻¹ * bas) (ψ.mulShift (β : k)) μ (cjLam t lam) Φ₀ κ →
        Core ν μX μG J bas ψ μ lam Φ κ := by sorry
