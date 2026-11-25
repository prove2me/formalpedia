-- Prove2me | Theorems.Thm_GlobalTheory_DegMove_exists_moved
-- name    : GlobalTheory.DegMove.exists_moved
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:06.549645+00:00
-- url     : https://prove2.me/theorems/9eff640b-5371-472b-ae39-7ea42070eb0b
-- title:
--   Deg Move: exists moved
-- statement:
--   The Deg Move construction uses the exists moved property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsHermFramePairNormalFormMovedByIsometry.lean#L284-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsHermFramePairNormalFormMovedByIsometry.lean#L284-L287

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometry
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
noncomputable section
open GlobalTheory GlobalTheory.DegMove

theorem GlobalTheory.DegMove.exists_moved : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (s : V ≃ₗ[K] V), s ∈ isomGrp H → ∃ N' : NF H r, (∀ a, N'.F.e a = s (N.F.e a) ∧ N'.F'.e a = s (N.F'.e a)) ∧ N'.j = N.j ∧ N'.c = N.c ∧ N'.T = N.T ∧ N'.𝔡 = N.𝔡 ∧ (∀ l, N'.nD l = N.nD l) ∧ ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), N'.om (s • Λ) = N.om Λ ∧ (N'.IsTerm g (s • Λ) ↔ N.IsTerm g Λ) ∧ N'.gI g (s • Λ) = N.gI g Λ := by sorry
