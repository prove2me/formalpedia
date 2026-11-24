-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_fiber_integral
-- name    : GlobalTheory.SplitWeil.HaarFactor.fiber_integral
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:32.25058+00:00
-- url     : https://prove2.me/theorems/870e60cc-92f6-4a74-b8e1-a19d21638660
-- title:
--   Haar Factor: fiber integral
-- statement:
--   The Haar Factor construction uses the fiber integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TranslationInvariantSchwartzBruhatMapFactorsInte.lean#L117-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TranslationInvariantSchwartzBruhatMapFactorsInte.lean#L117-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.HaarFactor
variable {X₀ A : Type*} [TopologicalSpace X₀] [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [T2Space X₀] [T2Space A]
variable [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]

theorem GlobalTheory.SplitWeil.HaarFactor.fiber_integral {U : AddSubgroup A} (hUo : IsOpen (U : Set A)) (hUc : IsCompact (U : Set A))
    {G : X₀ × A → ℂ} (T : Finset (A ⧸ U))
    (hT : ∀ z : X₀ × A, G z = ∑ q ∈ T, G (z.1, q.out) * (U : Set A).indicator (fun _ => (1 : ℂ)) (z.2 - q.out))
    (x : X₀) : ∫ a, G (x, a) ∂μ = (∑ q ∈ T, G (x, q.out)) * (μ.real (U : Set A) : ℂ) := by sorry
