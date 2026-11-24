-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreJointCont_continuousOn_integral_of_bounded
-- name    : GlobalTheory.CompanionTheory.SW.FibreJointCont.continuousOn_integral_of_bounded
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:04:21.382878+00:00
-- url     : https://prove2.me/theorems/785662d9-8651-40ae-80b7-75d20ab5718b
-- title:
--   Fibre Joint Cont: continuous On integral of bounded
-- statement:
--   The Fibre Joint Cont construction uses the continuous On integral of bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GermFormPulledBackCombinationsExpandMonomials.lean#L11-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GermFormPulledBackCombinationsExpandMonomials.lean#L11-L98

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUniqueStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuousStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermFormPulledBackCombinationsExpandMonomials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreJointCont

theorem GlobalTheory.CompanionTheory.SW.FibreJointCont.continuousOn_integral_of_bounded {V X P : Type}
    [TopologicalSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [TopologicalSpace P]
    (fib : X → Measure V) (B : Set X) (hB : IsOpen B)
    (hloc : ∀ b, IsLocallyFiniteMeasure (fib b))
    (hbd : ∀ (C : Set V) (D : Set X), IsCompact C → IsCompact D → D ⊆ B →
      ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c)
    (hcont : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ →
      ContinuousOn (fun b => ∫ v, φ v ∂(fib b)) B)
    (W : Set P) (Φ : P → V → ℝ)
    (hΦ : ContinuousOn (fun p : P × V => Φ p.1 p.2) (W ×ˢ Set.univ)) (hW : IsOpen W)
    (C : Set V) (hC : IsCompact C) (hsupp : ∀ p ∈ W, ∀ v, v ∉ C → Φ p v = 0) :
    ContinuousOn (fun q : P × X => ∫ v, Φ q.1 v ∂(fib q.2)) (W ×ˢ B) := by sorry
