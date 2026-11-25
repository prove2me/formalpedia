-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_nf_unique
-- name    : GlobalTheory.DegAsm.nf_unique
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:21:51.037628+00:00
-- url     : https://prove2.me/theorems/918b7482-1c5c-5c96-863b-94c79b44bece
-- title:
--   Deg Asm: nf unique
-- statement:
--   The Deg Asm construction uses the nf unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormUniqueUpToUnipotent.lean#L226-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormUniqueUpToUnipotent.lean#L226-L232

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormUniqueUpToUnipotent
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
open Formalism.HermitianLatticeCounting.P
open GlobalTheory GlobalTheory.DegAsm

theorem GlobalTheory.DegAsm.nf_unique : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (N₀ N₁ : NF H r), SameGr F N₀.F → SameGr F N₁.F → N₀.j = N₁.j → N₀.c = N₁.c → N₀.T = N₁.T → pairM N₀.F N₀.F' N₀.j = pairM N₁.F N₁.F' N₁.j → ∃ s : V ≃ₗ[K] V, F.InN (s : V →ₗ[K] V) ∧ ∀ a, s (N₀.F.e a) = N₁.F.e a ∧ s (N₀.F'.e a) = N₁.F'.e a := by sorry
