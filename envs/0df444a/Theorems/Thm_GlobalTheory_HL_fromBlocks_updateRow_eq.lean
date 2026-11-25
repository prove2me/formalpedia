-- Prove2me | Theorems.Thm_GlobalTheory_HL_fromBlocks_updateRow_eq
-- name    : GlobalTheory.HL.fromBlocks_updateRow_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:16:04.268131+00:00
-- url     : https://prove2.me/theorems/6fd3b406-aa13-558e-93f0-ae088b0e68ef
-- title:
--   HL: from Blocks update Row eq
-- statement:
--   The HL construction uses the from Blocks update Row eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetGramTwoFrames.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetGramTwoFrames.lean#L22-L28

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramTwoFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL

theorem GlobalTheory.HL.fromBlocks_updateRow_eq {R n : Type} [CommRing R] [Fintype n] [DecidableEq n]
    (Z Z' : Matrix n n R) (l : n) (a b c d : n → R) :
    ((Matrix.fromBlocks Z 0 0 Z').updateRow (Sum.inl l) (Sum.elim a b)).updateRow (Sum.inr l)
        (Sum.elim c d) =
      Matrix.fromBlocks (Z.updateRow l a) ((0 : Matrix n n R).updateRow l b)
        ((0 : Matrix n n R).updateRow l c) (Z'.updateRow l d) := by sorry
