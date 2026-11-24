-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_PartialFourier_partial_mem_SB
-- name    : GlobalTheory.LocFlat.PartialFourier.partial_mem_SB
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:26:19.640599+00:00
-- url     : https://prove2.me/theorems/7d7a50e3-744f-4f6c-88c1-54d625a3faf7
-- title:
--   Partial Fourier: partial mem SB
-- statement:
--   The Partial Fourier construction uses the partial mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialFourierInversion.lean#L37-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialFourierInversion.lean#L37-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialFourierInversion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.PartialFourier
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
omit [BorelSpace k]

theorem GlobalTheory.LocFlat.PartialFourier.partial_mem_SB {I J : Type} [Fintype I] [Fintype J] (ν : Measure k) {f : (I → k) × (J → k) → ℂ}
    (hf : f ∈ SB ((I → k) × (J → k))) :
    (fun x₁ : I → k => ∫ y : J → k, f (x₁, y) ∂(Measure.pi fun _ => ν)) ∈ SB (I → k) := by sorry
