-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_hermFramePairNormalForm_moved_by_isometry
-- name    : GlobalTheory.T.exists_hermFramePairNormalForm_moved_by_isometry
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:34.312934+00:00
-- url     : https://prove2.me/theorems/a588b020-d08c-4a67-9750-cfe8453aeed2
-- title:
--   T: exists herm Frame Pair Normal Form moved by isometry
-- statement:
--   The T construction uses the exists herm Frame Pair Normal Form moved by isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsHermFramePairNormalFormMovedByIsometryStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsHermFramePairNormalFormMovedByIsometryStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometry
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometryStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_hermFramePairNormalForm_moved_by_isometry : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (s : V ≃ₗ[K] V), s ∈ isomGrp H → ∃ N' : NF H r, (∀ a, N'.F.e a = s (N.F.e a) ∧ N'.F'.e a = s (N.F'.e a)) ∧ N'.j = N.j ∧ N'.c = N.c ∧ N'.T = N.T ∧ N'.𝔡 = N.𝔡 ∧ (∀ l, N'.nD l = N.nD l) ∧ ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), N'.om (s • Λ) = N.om Λ ∧ (N'.IsTerm g (s • Λ) ↔ N.IsTerm g Λ) ∧ N'.gI g (s • Λ) = N.gI g Λ := by sorry
