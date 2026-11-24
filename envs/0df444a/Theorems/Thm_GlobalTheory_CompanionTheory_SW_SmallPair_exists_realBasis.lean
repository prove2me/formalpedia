-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SmallPair_exists_realBasis
-- name    : GlobalTheory.CompanionTheory.SW.SmallPair.exists_realBasis
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:51.621659+00:00
-- url     : https://prove2.me/theorems/f5dcf7ce-7f9c-40e2-87db-8388987286a2
-- title:
--   Small Pair: exists real Basis
-- statement:
--   The Small Pair construction uses the exists real Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCuspReductionBound.lean#L7-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCuspReductionBound.lean#L7-L33

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCuspReductionBound
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SmallPair

theorem GlobalTheory.CompanionTheory.SW.SmallPair.exists_realBasis {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F)
    (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis κ ℝ (InfinitePlace F → ℝ)),
      ∀ i, ∃ a : 𝓞 F, ∀ w, b i w = ρ w (a : F) := by sorry
