-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_opE_SB_and_linear
-- name    : GlobalTheory.RootEx.opE_SB_and_linear
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:40.224982+00:00
-- url     : https://prove2.me/theorems/82896785-13fc-4ec7-b38f-7da9d7004090
-- title:
--   Root Ex: op E SB and linear
-- statement:
--   The Root Ex construction uses the op E SB and linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClosedEmbeddingAffPtUncurry.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClosedEmbeddingAffPtUncurry.lean#L154-L156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx

theorem GlobalTheory.RootEx.opE_SB_and_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure], (∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), opE ψ ν p Φ ∈ SB (Matrix n n' k)) ∧ ∀ (z : ℂ), ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ Ψ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), opE ψ ν p (z • Φ + Ψ) = z • opE ψ ν p Φ + opE ψ ν p Ψ := by sorry
