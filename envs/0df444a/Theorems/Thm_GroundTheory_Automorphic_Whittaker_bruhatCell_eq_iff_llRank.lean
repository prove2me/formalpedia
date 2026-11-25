-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_eq_iff_llRank
-- name    : GroundTheory.Automorphic.Whittaker.bruhatCell_eq_iff_llRank
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:56.921739+00:00
-- url     : https://prove2.me/theorems/2dae641e-e518-4819-9103-adfff9aac6b8
-- title:
--   Whittaker: bruhat Cell eq iff ll Rank
-- statement:
--   The Whittaker construction uses the bruhat Cell eq iff ll Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L314-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L314-L323

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

theorem GroundTheory.Automorphic.Whittaker.bruhatCell_eq_iff_llRank {g g' : GL (Fin n) F} :
    bruhatCell g = bruhatCell g' ↔ ∀ i j, llRank i j g = llRank i j g' := by sorry
