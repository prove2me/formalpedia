-- Prove2me | Theorems.Thm_GlobalTheory_FlatSourceStable_flat_ne_zero_of_mem_R
-- name    : GlobalTheory.FlatSourceStable.flat_ne_zero_of_mem_R
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:48:44.600521+00:00
-- url     : https://prove2.me/theorems/fc6e84e2-59a4-51e1-a4e9-0556cddb5053
-- title:
--   Flat Source Stable: flat ne zero of mem R
-- statement:
--   The Flat Source Stable construction uses the flat ne zero of mem R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatNeZeroOfMemR.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatNeZeroOfMemR.lean#L22-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatNeZeroOfMemR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.FlatSourceStable

theorem GlobalTheory.FlatSourceStable.flat_ne_zero_of_mem_R : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ) (g : GL (n' ⊕ Fin (c + 1 + 1)) k) (h : GL (n ⊕ Fin (c + 1)) k), flat ψ ν μ Φ g h ≠ 0 → ∀ r ∈ R k n' (c + 1 + 1) 1, flat ψ ν μ Φ (r * g) h ≠ 0 := by sorry
