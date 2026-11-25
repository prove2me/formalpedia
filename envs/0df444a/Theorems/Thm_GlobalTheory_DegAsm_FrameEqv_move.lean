-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_FrameEqv_move
-- name    : GlobalTheory.DegAsm.FrameEqv.move
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:23:44.922085+00:00
-- url     : https://prove2.me/theorems/ffa41403-482d-4b69-bbe7-561bfc596fa1
-- title:
--   Frame Eqv: move
-- statement:
--   The Frame Eqv construction uses the move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrEqvEquivalence.lean#L94-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrEqvEquivalence.lean#L94-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrEqvEquivalence
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
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.FrameEqv
open AdaptInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem GlobalTheory.DegAsm.FrameEqv.move (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {F G G' : FlagD H r} {𝔡 : Ideal (𝓞 K)} {Λ : Submodule (𝓞 K) V}
    (h : FrEqv F Λ G G') (N : NF H r) (hN : Adapt F G 𝔡 N) :
    ∃ N' : NF H r, Adapt F G' 𝔡 N' ∧ N'.om Λ = N.om Λ ∧
      ∀ g : ℕ, (N'.IsTerm g Λ ↔ N.IsTerm g Λ) ∧ N'.gI g Λ = N.gI g Λ := by sorry
