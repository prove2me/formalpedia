-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatSum_fibre_card
-- name    : GlobalTheory.CompanionTheory.SW.LatSum.fibre_card
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:06:55.482249+00:00
-- url     : https://prove2.me/theorems/c9ba74f2-cf86-4c5a-8751-66f8cab4a5b2
-- title:
--   Lat Sum: fibre card
-- statement:
--   The Lat Sum construction uses the fibre card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L179-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L179-L202

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EisensteinLatticeSumBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatSum
open Classical

theorem GlobalTheory.CompanionTheory.SW.LatSum.fibre_card (F : Type) [Field F] [NumberField F] (ρ : InfinitePlace F → (F →+* ℝ))
    (S : Finset (𝓞 F)) (hS : ∀ α : 𝓞 F, (∀ w, |ρ w (α : F)| < 1) → α ∈ S)
    (x : InfinitePlace F → ℝ) (T : Finset (𝓞 F)) (n : InfinitePlace F → ℤ) :
    (T.filter fun r : 𝓞 F => (fun w => ⌊x w + ρ w (r : F)⌋) = n).card ≤ S.card := by sorry
