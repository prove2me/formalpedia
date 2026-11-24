-- Prove2me | Theorems.Thm_GlobalTheory_CollapseCompare_exists_rescaled
-- name    : GlobalTheory.CollapseCompare.exists_rescaled
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:19:35.270821+00:00
-- url     : https://prove2.me/theorems/221f6dbf-67ec-494a-b143-dba2788cc0f1
-- title:
--   Collapse Compare: exists rescaled
-- statement:
--   The Collapse Compare construction uses the exists rescaled property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CoreIffCollapsesWith.lean#L465-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CoreIffCollapsesWith.lean#L465-L495

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

theorem GlobalTheory.CollapseCompare.exists_rescaled (β : kˣ) (ν ν₀ : Measure k) [ν.IsAddHaarMeasure] [ν₀.IsAddHaarMeasure]
    {t : GL (n ⊕ Fin c) k} (ht : t = frame n c fun i => 1⁻¹ * β⁻¹ ^ i)
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Φ ∈ SB _) :
    ∃ Φ₀ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      (∀ ψ μ h, flat (ψ.mulShift (β : k)) ν₀ μ Φ₀ 1 h = flat ψ ν μ Φ 1 (t * h * t⁻¹)) ∧
      ∀ μ h (z : ℂ), om μ 1 (t * h * t⁻¹) Φ = z • Φ → om μ 1 h Φ₀ = z • Φ₀ := by sorry
