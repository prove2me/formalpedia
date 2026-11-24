-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_map_eq_zero_of_fiber
-- name    : GlobalTheory.SplitWeil.HaarFactor.map_eq_zero_of_fiber
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:21:40.051837+00:00
-- url     : https://prove2.me/theorems/58f49edd-f476-4092-9a45-206d2bf255af
-- title:
--   Haar Factor: map eq zero of fiber
-- statement:
--   The Haar Factor construction uses the map eq zero of fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TranslationInvariantSchwartzBruhatMapFactorsInte.lean#L134-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TranslationInvariantSchwartzBruhatMapFactorsInte.lean#L134-L160

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

theorem GlobalTheory.SplitWeil.HaarFactor.map_eq_zero_of_fiber
    (hbasis : ∀ V ∈ 𝓝 (0 : A), ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧ (U : Set A) ⊆ V)
    {M : Type*} [AddCommGroup M] [Module ℂ M] (L : SB (X₀ × A) →ₗ[ℂ] M)
    (hL : ∀ (a : A) (G G' : SB (X₀ × A)), (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L G' = L G)
    (G : SB (X₀ × A)) (hG : ∀ x, ∫ a, G.1 (x, a) ∂μ = 0) : L G = 0 := by sorry
