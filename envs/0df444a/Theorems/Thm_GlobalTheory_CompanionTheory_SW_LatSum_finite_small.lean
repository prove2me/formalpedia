-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatSum_finite_small
-- name    : GlobalTheory.CompanionTheory.SW.LatSum.finite_small
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:07:18.261505+00:00
-- url     : https://prove2.me/theorems/f80b008e-a69d-4441-b499-cfc593d330bb
-- title:
--   Lat Sum: finite small
-- statement:
--   The Lat Sum construction uses the finite small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L123-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L123-L134

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

theorem GlobalTheory.CompanionTheory.SW.LatSum.finite_small (F : Type) [Field F] [NumberField F] (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    {α : 𝓞 F | ∀ w, |ρ w (α : F)| < 1}.Finite := by sorry
