-- Prove2me | Theorems.Thm_GroundTheory_Brauer_nonempty_algEquiv_matrix_of_matrix
-- name    : GroundTheory.Brauer.nonempty_algEquiv_matrix_of_matrix
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:14:12.470294+00:00
-- url     : https://prove2.me/theorems/03d768b2-5bcc-57af-883f-6a139a1c0093
-- title:
--   Brauer: nonempty alg Equiv matrix of matrix
-- statement:
--   The Brauer construction uses the nonempty alg Equiv matrix of matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L347-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L347-L354

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

theorem GroundTheory.Brauer.nonempty_algEquiv_matrix_of_matrix {L : Type*} [Field L] [Algebra K L] {D : Type*}
    [Ring D] [Algebra K D] {m k : ℕ} (eA : A ≃ₐ[K] Matrix (Fin m) (Fin m) D)
    (eD : L ⊗[K] D ≃ₐ[L] Matrix (Fin k) (Fin k) L) :
    Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin (m * k)) (Fin (m * k)) L) := by sorry
