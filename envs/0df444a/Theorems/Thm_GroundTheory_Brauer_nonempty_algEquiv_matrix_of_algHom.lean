-- Prove2me | Theorems.Thm_GroundTheory_Brauer_nonempty_algEquiv_matrix_of_algHom
-- name    : GroundTheory.Brauer.nonempty_algEquiv_matrix_of_algHom
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:14:07.272863+00:00
-- url     : https://prove2.me/theorems/b06d6685-86b1-5f5c-a85d-4f99c3bf5aff
-- title:
--   Brauer: nonempty alg Equiv matrix of alg Hom
-- statement:
--   The Brauer construction uses the nonempty alg Equiv matrix of alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L132-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L132-L153

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct Module
universe u v w
variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A] {L : Type*} [Field L]
  [Algebra K L]
open RightMul

theorem GroundTheory.Brauer.nonempty_algEquiv_matrix_of_algHom [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] (ι : L →ₐ[K] A) (h : finrank K L ^ 2 = finrank K A) :
    Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin (finrank K L)) (Fin (finrank K L)) L) := by sorry
