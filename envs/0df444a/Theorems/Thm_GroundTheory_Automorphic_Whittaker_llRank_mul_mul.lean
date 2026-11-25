-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_llRank_mul_mul
-- name    : GroundTheory.Automorphic.Whittaker.llRank_mul_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:29:18.488993+00:00
-- url     : https://prove2.me/theorems/cc831d2d-ce7c-4411-87e8-c4bec4b5ceea
-- title:
--   Whittaker: ll Rank mul mul
-- statement:
--   The Whittaker construction uses the ll Rank mul mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L130-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L130-L172

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

theorem GroundTheory.Automorphic.Whittaker.llRank_mul_mul {b b' : GL (Fin n) F} (hb : b ∈ borel n F) (hb' : b' ∈ borel n F)
    (i j : Fin n) (g : GL (Fin n) F) : llRank i j (b * g * b') = llRank i j g := by sorry
