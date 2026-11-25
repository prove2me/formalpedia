-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_submatrix_mul_of_isUpperTriangular
-- name    : GroundTheory.Automorphic.Whittaker.submatrix_mul_of_isUpperTriangular
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:07:59.515783+00:00
-- url     : https://prove2.me/theorems/17a65642-3a71-499b-b8f8-fb3d67b072b0
-- title:
--   Whittaker: submatrix mul of is Upper Triangular
-- statement:
--   The Whittaker construction uses the submatrix mul of is Upper Triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L432-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L432-L447

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

theorem GroundTheory.Automorphic.Whittaker.submatrix_mul_of_isUpperTriangular {u M : Matrix (Fin n) (Fin n) F}
    (hu : u.IsUpperTriangular) {m p : ℕ} {r : Fin m → Fin n} (hr : Function.Injective r)
    (hup : ∀ a s, r a ≤ s → ∃ b, r b = s) (c : Fin p → Fin n) :
    (u * M).submatrix r c = u.submatrix r r * M.submatrix r c := by sorry
