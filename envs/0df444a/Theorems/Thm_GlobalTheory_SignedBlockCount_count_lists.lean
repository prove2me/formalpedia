-- Prove2me | Theorems.Thm_GlobalTheory_SignedBlockCount_count_lists
-- name    : GlobalTheory.SignedBlockCount.count_lists
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:08.936442+00:00
-- url     : https://prove2.me/theorems/4247bbcf-de76-552a-b0ec-306d67afc0fc
-- title:
--   Signed Block Count: count lists
-- statement:
--   The Signed Block Count construction uses the count lists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SignedBlockAntidiagWithLeadingMinorsEncardLe.lean#L62-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SignedBlockAntidiagWithLeadingMinorsEncardLe.lean#L62-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SignedBlockAntidiagWithLeadingMinorsEncardLe
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
open GlobalTheory GlobalTheory.SignedBlockCount
open Formalism.MainNotions.S.Loc
variable {K : Type} [Field K]

theorem GlobalTheory.SignedBlockCount.count_lists (n : ℕ) : ∀ η : ℕ → K, ∃ T : Finset (List (Kˣ × ℕ+)), T.card ≤ 2 ^ n ∧
    ∀ bs : List (Kˣ × ℕ+), (bs.map (fun b => (b.2 : ℕ))).sum = n →
      (∀ l ≤ n, minor bs l = η l) → bs ∈ T := by sorry
