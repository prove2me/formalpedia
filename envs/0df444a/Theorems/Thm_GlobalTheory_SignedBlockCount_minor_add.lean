-- Prove2me | Theorems.Thm_GlobalTheory_SignedBlockCount_minor_add
-- name    : GlobalTheory.SignedBlockCount.minor_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:54:05.224058+00:00
-- url     : https://prove2.me/theorems/2806cfba-069c-5055-a4e1-85b03086147f
-- title:
--   Signed Block Count: minor add
-- statement:
--   The Signed Block Count construction uses the minor add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SignedBlockAntidiagWithLeadingMinorsEncardLe.lean#L26-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SignedBlockAntidiagWithLeadingMinorsEncardLe.lean#L26-L47

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

theorem GlobalTheory.SignedBlockCount.minor_add (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) (l : ℕ) :
    minor ((t, s) :: bs) (s + l) =
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ) *
        (t : K) ^ (s : ℕ)) * minor bs l := by sorry
