-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_InvariantProduct_exists_const_rect
-- name    : GlobalTheory.CompanionTheory.SW.InvariantProduct.exists_const_rect
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:06:43.332947+00:00
-- url     : https://prove2.me/theorems/0f0a408f-8897-4c55-ab35-ba2997eae3a3
-- title:
--   Invariant Product: exists const rect
-- statement:
--   The Invariant Product construction uses the exists const rect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MeasureEqHaarProdOfLeftInvariant.lean#L9-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MeasureEqHaarProdOfLeftInvariant.lean#L9-L39

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.InvariantProduct

theorem GlobalTheory.CompanionTheory.SW.InvariantProduct.exists_const_rect {Q Z : Type} [Group Q] [TopologicalSpace Q] [LocallyCompactSpace Q]
    [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
    [IsTopologicalGroup Q] [TopologicalSpace Z] [T2Space Z]
    [MeasurableSpace Z] [BorelSpace Z] (η : Measure Q) [η.IsHaarMeasure]
    (ρ : Measure (Q × Z)) [IsLocallyFiniteMeasure ρ]
    (hinv : ∀ q : Q, ρ.map (fun p => (q * p.1, p.2)) = ρ)
    {A C : Set Z} (hA : MeasurableSet A) (hC : IsCompact C) (hAC : A ⊆ C) :
    ∃ c : ℝ≥0, ∀ U : Set Q, MeasurableSet U → ρ (U ×ˢ A) = c * η U := by sorry
