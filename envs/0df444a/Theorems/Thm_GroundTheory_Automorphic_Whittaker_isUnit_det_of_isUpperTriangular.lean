-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_isUnit_det_of_isUpperTriangular
-- name    : GroundTheory.Automorphic.Whittaker.isUnit_det_of_isUpperTriangular
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:41:00.996041+00:00
-- url     : https://prove2.me/theorems/43d36418-d20c-4723-aa39-c001f150fb6d
-- title:
--   Whittaker: is Unit det of is Upper Triangular
-- statement:
--   The Whittaker construction uses the is Unit det of is Upper Triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L125-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L125-L128

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

theorem GroundTheory.Automorphic.Whittaker.isUnit_det_of_isUpperTriangular {X : Matrix (Fin n) (Fin n) F} (hX : X.IsUpperTriangular)
    (hd : ∀ r, X r r ≠ 0) : IsUnit X.det := by sorry
