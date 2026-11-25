-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_DatCount_exists_fun_span
-- name    : GlobalTheory.DegCnt.DatCount.exists_fun_span
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:16:46.970846+00:00
-- url     : https://prove2.me/theorems/80deb5df-95e5-5a00-9ab6-a7d70fff04c3
-- title:
--   Dat Count: exists fun span
-- statement:
--   The Dat Count construction uses the exists fun span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardEmbeddedDataWithGivenFixedLattice.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardEmbeddedDataWithGivenFixedLattice.lean#L18-L31

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
variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem GlobalTheory.DegCnt.DatCount.exists_fun_span (t : Finset V) {e : ℕ} (hc : t.card ≤ e) :
    ∃ g : Fin e → V, Submodule.span R (Set.range g) = Submodule.span R (t : Set V) := by sorry
