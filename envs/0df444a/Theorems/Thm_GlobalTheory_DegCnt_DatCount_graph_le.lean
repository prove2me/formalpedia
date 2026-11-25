-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_DatCount_graph_le
-- name    : GlobalTheory.DegCnt.DatCount.graph_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:13.343464+00:00
-- url     : https://prove2.me/theorems/c78a2f53-b370-426f-8a55-29fc4a1b83e0
-- title:
--   Dat Count: graph le
-- statement:
--   The Dat Count construction uses the graph le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardEmbeddedDataWithGivenFixedLattice.lean#L190-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardEmbeddedDataWithGivenFixedLattice.lean#L190-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEmbeddedDataWithGivenFixedLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.DatCount
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [NumberField K] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.DegCnt.DatCount.graph_le {H : HermSpace K V} {g : 𝓞 K} {L' L : Submodule (𝓞 K) V}
    {Γ₁ Γ₂ : Submodule (𝓞 K) (V × V)} (h1 : IsModIso H g L' L Γ₁) (h2 : IsModIso H g L' L Γ₂)
    (hf : fixLat Γ₁ = fixLat Γ₂) {S : Set V} (hS : L' = fixLat Γ₁ ⊔ Submodule.span (𝓞 K) S)
    (hs : ∀ s ∈ S, ∃ y, (s, y) ∈ Γ₁ ∧ (s, y) ∈ Γ₂) : Γ₁ ≤ Γ₂ := by sorry
