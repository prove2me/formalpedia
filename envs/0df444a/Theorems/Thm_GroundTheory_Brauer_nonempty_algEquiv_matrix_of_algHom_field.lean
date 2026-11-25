-- Prove2me | Theorems.Thm_GroundTheory_Brauer_nonempty_algEquiv_matrix_of_algHom_field
-- name    : GroundTheory.Brauer.nonempty_algEquiv_matrix_of_algHom_field
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:14:14.139093+00:00
-- url     : https://prove2.me/theorems/856ae8cf-636b-5cfa-96f4-8791a4893544
-- title:
--   Brauer: nonempty alg Equiv matrix of alg Hom field
-- statement:
--   The Brauer construction uses the nonempty alg Equiv matrix of alg Hom field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L337-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L337-L345

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
variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]

theorem GroundTheory.Brauer.nonempty_algEquiv_matrix_of_algHom_field {L : Type*} [Field L] [Algebra K L] {E : Type*}
    [Field E] [Algebra K E] (σ : L →ₐ[K] E) {n : ℕ}
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Nonempty (E ⊗[K] A ≃ₐ[E] Matrix (Fin n) (Fin n) E) := by sorry
