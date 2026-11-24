-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_basis_prod
-- name    : GlobalTheory.SplitWeil.HaarFactor.basis_prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:22:02.356629+00:00
-- url     : https://prove2.me/theorems/72522feb-1b7e-497c-bd4f-c30e321cb832
-- title:
--   Haar Factor: basis prod
-- statement:
--   The Haar Factor construction uses the basis prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TranslationInvariantSchwartzBruhatMapFactorsInte.lean#L211-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TranslationInvariantSchwartzBruhatMapFactorsInte.lean#L211-L223

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
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SplitWeil.HaarFactor.basis_prod (m₁ m₂ : Type*) [Fintype m₁] [Fintype m₂] :
    ∀ V ∈ 𝓝 (0 : (m₁ → k) × (m₂ → k)), ∃ U : AddSubgroup ((m₁ → k) × (m₂ → k)),
      IsOpen (U : Set ((m₁ → k) × (m₂ → k))) ∧ IsCompact (U : Set ((m₁ → k) × (m₂ → k))) ∧
        (U : Set ((m₁ → k) × (m₂ → k))) ⊆ V := by sorry
