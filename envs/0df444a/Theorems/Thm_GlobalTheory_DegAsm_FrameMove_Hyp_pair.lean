-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_FrameMove_Hyp_pair
-- name    : GlobalTheory.DegAsm.FrameMove.Hyp.pair
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:21:57.032156+00:00
-- url     : https://prove2.me/theorems/573f0d93-0dbb-5890-a3f8-5c57fbb4eb4c
-- title:
--   Hyp: pair
-- statement:
--   The Hyp construction uses the pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SmulMemOfOne.lean#L112-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SmulMemOfOne.lean#L112-L119

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
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem GlobalTheory.DegAsm.FrameMove.Hyp.pair {e y : Fin r → V} (h : Hyp H e y) (s t s' t' : Fin r → K) {n n' : V}
    (h1 : ∀ a, H.B n (e a) = 0) (h2 : ∀ a, H.B n (y a) = 0) (h3 : ∀ a, H.B n' (e a) = 0) (h4 : ∀ a, H.B n' (y a) = 0) :
    H.B (∑ a, s a • e a + ∑ a, t a • y a + n) (∑ a, s' a • e a + ∑ a, t' a • y a + n') =
      ∑ a, s a * star (t' a) + ∑ a, t a * star (s' a) + H.B n n' := by sorry
