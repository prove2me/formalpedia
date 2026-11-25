-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_perm_eq_of_llRank
-- name    : GroundTheory.Automorphic.Whittaker.perm_eq_of_llRank
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:56:55.600846+00:00
-- url     : https://prove2.me/theorems/0799f5ca-790e-4257-843f-d25ed5502b60
-- title:
--   Whittaker: perm eq of ll Rank
-- statement:
--   The Whittaker construction uses the perm eq of ll Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L249-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L249-L276

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

theorem GroundTheory.Automorphic.Whittaker.perm_eq_of_llRank {w w' : Equiv.Perm (Fin n)}
    (h : ∀ i j, llRank i j (permGL F w) = llRank i j (permGL F w')) : w = w' := by sorry
