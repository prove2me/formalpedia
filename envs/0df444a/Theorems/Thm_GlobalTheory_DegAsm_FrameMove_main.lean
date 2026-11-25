-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_FrameMove_main
-- name    : GlobalTheory.DegAsm.FrameMove.main
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:31:04.97906+00:00
-- url     : https://prove2.me/theorems/4b39a770-aa54-4bbd-82aa-13660a07eec3
-- title:
--   Frame Move: main
-- statement:
--   The Frame Move construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SmulMemOfOne.lean#L343-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SmulMemOfOne.lean#L343-L420

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SmulMemOfOne
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
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.FrameMove

theorem GlobalTheory.DegAsm.FrameMove.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G : FlagD H r) (aa : Fin r → Submodule (𝓞 K) K) (Λ : Submodule (𝓞 K) V), IsUnimod H Λ → IsFrame F Λ aa → SameGr F G → F.T = G.T → (∀ a, ∀ t ∈ aa a, t • F.e a.castSucc ∈ Λ ∧ t • G.e a.castSucc ∈ Λ) → F.z ∈ Λ → G.z ∈ Λ → ∃ m : V ≃ₗ[K] V, F.InN (m : V →ₗ[K] V) ∧ m • Λ = Λ ∧ ∀ a, m (F.e a) = G.e a := by sorry
