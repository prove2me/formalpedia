-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_llRank_permGL
-- name    : GroundTheory.Automorphic.Whittaker.llRank_permGL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:29:26.175976+00:00
-- url     : https://prove2.me/theorems/40916b4d-aae4-42f4-8c63-2ce674c26a8b
-- title:
--   Whittaker: ll Rank perm GL
-- statement:
--   The Whittaker construction uses the ll Rank perm GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L174-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L174-L197

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

theorem GroundTheory.Automorphic.Whittaker.llRank_permGL (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    llRank i j (permGL F w) = (Finset.univ.filter fun r : Fin n => i ≤ r ∧ w⁻¹ r ≤ j).card := by sorry
