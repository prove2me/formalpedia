-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_DatMove_flag_vector_mem_base_lattice
-- name    : GlobalTheory.DegAsm.DatMove.flag_vector_mem_base_lattice
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:25:53.091667+00:00
-- url     : https://prove2.me/theorems/a4f9ffd1-98a1-41b1-b8bd-3e561ac81d73
-- title:
--   Dat Move: flag vector mem base lattice
-- statement:
--   The Dat Move construction uses the flag vector mem base lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EmbeddedDatumInvariantUnderUnipotent.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EmbeddedDatumInvariantUnderUnipotent.lean#L114-L117

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
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
variable (s : V ≃ₗ[K] V) (hs : ∀ x y, H.B (s x) (s y) = H.B x y)
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]

theorem GlobalTheory.DegAsm.DatMove.flag_vector_mem_base_lattice (F G : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F G := by sorry
