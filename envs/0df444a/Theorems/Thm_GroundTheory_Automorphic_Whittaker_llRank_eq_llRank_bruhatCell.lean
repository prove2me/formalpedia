-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_llRank_eq_llRank_bruhatCell
-- name    : GroundTheory.Automorphic.Whittaker.llRank_eq_llRank_bruhatCell
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:58.864907+00:00
-- url     : https://prove2.me/theorems/913c9981-d548-4213-b554-c155f375d70d
-- title:
--   Whittaker: ll Rank eq ll Rank bruhat Cell
-- statement:
--   The Whittaker construction uses the ll Rank eq ll Rank bruhat Cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L308-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L308-L312

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}

theorem GroundTheory.Automorphic.Whittaker.llRank_eq_llRank_bruhatCell (i j : Fin n) (g : GL (Fin n) F) :
    llRank i j g = llRank i j (permGL F (bruhatCell g)) := by sorry
