-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_om_isSmoothRepresentation
-- name    : GlobalTheory.SplitWeil.om_isSmoothRepresentation
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:31.212438+00:00
-- url     : https://prove2.me/theorems/faabc75d-4104-47f5-911d-13c72a81419e
-- title:
--   Split Weil: om is Smooth Representation
-- statement:
--   The Split Weil construction uses the om is Smooth Representation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyCompSideMulEq.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyCompSideMulEq.lean#L102-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
open GlobalTheory GlobalTheory.SplitWeil

theorem GlobalTheory.SplitWeil.om_isSmoothRepresentation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)), (∀ Φ : Matrix b a k → ℂ, om μ 1 1 Φ = Φ) ∧ (∀ (g g' : GL a k) (h h' : GL b k) (Φ : Matrix b a k → ℂ), om μ (g * g') (h * h') Φ = om μ g h (om μ g' h' Φ)) ∧ (∀ (g : GL a k) (h : GL b k) (z : ℂ) (Φ Ψ : Matrix b a k → ℂ), om μ g h (z • Φ + Ψ) = z • om μ g h Φ + om μ g h Ψ) ∧ (∀ (g : GL a k) (h : GL b k), ∀ Φ ∈ SB (Matrix b a k), om μ g h Φ ∈ SB (Matrix b a k)) ∧ ∀ Φ ∈ SB (Matrix b a k), IsOpen {gh : GL a k × GL b k | om μ gh.1 gh.2 Φ = Φ} := by sorry
