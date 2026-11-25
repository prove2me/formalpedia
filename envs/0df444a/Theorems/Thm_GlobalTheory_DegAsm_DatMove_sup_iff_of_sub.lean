-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_DatMove_sup_iff_of_sub
-- name    : GlobalTheory.DegAsm.DatMove.sup_iff_of_sub
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:23:23.337203+00:00
-- url     : https://prove2.me/theorems/b014afd0-3b0c-46f3-9aac-325ef86e0596
-- title:
--   Dat Move: sup iff of sub
-- statement:
--   The Dat Move construction uses the sup iff of sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EmbeddedDatumInvariantUnderUnipotent.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EmbeddedDatumInvariantUnderUnipotent.lean#L26-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EmbeddedDatumInvariantUnderUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.DatMove
open AdaptInv

theorem GlobalTheory.DegAsm.DatMove.sup_iff_of_sub {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (t : M ≃+ M)
    {A B C : Submodule R M} (h : ∀ y, t y ∈ A ↔ y ∈ B) (h' : ∀ y, t y ∈ C ↔ y ∈ C) {y : M}
    (hy : t y - y ∈ C) : y ∈ A ⊔ C ↔ y ∈ B ⊔ C := by sorry
