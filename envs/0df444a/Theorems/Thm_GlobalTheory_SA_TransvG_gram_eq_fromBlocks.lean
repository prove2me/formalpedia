-- Prove2me | Theorems.Thm_GlobalTheory_SA_TransvG_gram_eq_fromBlocks
-- name    : GlobalTheory.SA.TransvG.gram_eq_fromBlocks
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:46:02.071193+00:00
-- url     : https://prove2.me/theorems/c0e6eb36-53b3-465c-b2e2-9d6752614ff8
-- title:
--   Transv G: gram eq from Blocks
-- statement:
--   The Transv G construction uses the gram eq from Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetFromBlocksSingle.lean#L88-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetFromBlocksSingle.lean#L88-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetFromBlocksSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA Matrix
open GlobalTheory GlobalTheory.SA GlobalTheory.SA.TransvG
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem GlobalTheory.SA.TransvG.gram_eq_fromBlocks (F F' : FlagD H r) :
    Gram F F' = fromBlocks (diagonal fun a => if a = Fin.last r then -F.T else 0) (Zhat F F') (Zhat F F')ᴴ
      (diagonal fun a => if a = Fin.last r then -F'.T else 0) := by sorry
