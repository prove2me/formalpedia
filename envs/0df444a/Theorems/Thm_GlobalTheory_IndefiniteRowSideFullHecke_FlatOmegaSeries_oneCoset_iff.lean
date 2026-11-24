-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FlatOmegaSeries_oneCoset_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries.oneCoset_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:02:24.876621+00:00
-- url     : https://prove2.me/theorems/8f8c734d-62a4-4bb3-82c8-e1ea0568d87f
-- title:
--   Flat Omega Series: one Coset iff
-- statement:
--   The Flat Omega Series construction uses the one Coset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/SiegelEisenstein/FlatOmegaSeries.lean#L55-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/SiegelEisenstein/FlatOmegaSeries.lean#L55-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_FlatOmegaSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {P P' A : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P'] [AddCommGroup A] [Module ℂ A]
variable [MeasurableSpace k] [BorelSpace k]
omit [BorelSpace k]

theorem GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries.oneCoset_iff (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (J : Subgroup (GL (n ⊕ Fin c) k)) :
    OneCoset ψ ν μ Φ J ↔ ∀ h, flat ψ ν μ Φ 1 h ≠ 0 → ∃ r ∈ R k n c 1, ∃ κ ∈ J, h = r * κ := by sorry
