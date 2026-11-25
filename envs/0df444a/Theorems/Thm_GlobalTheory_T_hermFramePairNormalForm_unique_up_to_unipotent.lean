-- Prove2me | Theorems.Thm_GlobalTheory_T_hermFramePairNormalForm_unique_up_to_unipotent
-- name    : GlobalTheory.T.hermFramePairNormalForm_unique_up_to_unipotent
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:51:47.981215+00:00
-- url     : https://prove2.me/theorems/c94c4134-32f7-565c-818d-af617b076a19
-- title:
--   T: herm Frame Pair Normal Form unique up to unipotent
-- statement:
--   The T construction uses the herm Frame Pair Normal Form unique up to unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormUniqueUpToUnipotentStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormUniqueUpToUnipotentStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormUniqueUpToUnipotent
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormUniqueUpToUnipotentStatement
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

theorem GlobalTheory.T.hermFramePairNormalForm_unique_up_to_unipotent : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (N₀ N₁ : NF H r), SameGr F N₀.F → SameGr F N₁.F → N₀.j = N₁.j → N₀.c = N₁.c → N₀.T = N₁.T → pairM N₀.F N₀.F' N₀.j = pairM N₁.F N₁.F' N₁.j → ∃ s : V ≃ₗ[K] V, F.InN (s : V →ₗ[K] V) ∧ ∀ a, s (N₀.F.e a) = N₁.F.e a ∧ s (N₀.F'.e a) = N₁.F'.e a := by sorry
