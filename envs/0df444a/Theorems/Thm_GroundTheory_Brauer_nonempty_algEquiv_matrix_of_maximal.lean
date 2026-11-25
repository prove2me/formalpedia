-- Prove2me | Theorems.Thm_GroundTheory_Brauer_nonempty_algEquiv_matrix_of_maximal
-- name    : GroundTheory.Brauer.nonempty_algEquiv_matrix_of_maximal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:14:18.7369+00:00
-- url     : https://prove2.me/theorems/92255dbb-6ca9-5d6d-a35a-1bb034759365
-- title:
--   Brauer: nonempty alg Equiv matrix of maximal
-- statement:
--   The Brauer construction uses the nonempty alg Equiv matrix of maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L233-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L233-L240

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
variable {K : Type*} [Field K] {D : Type*} [DivisionRing D] [Algebra K D]
variable [Algebra.IsCentral K D] [FiniteDimensional K D]

theorem GroundTheory.Brauer.nonempty_algEquiv_matrix_of_maximal (F : Subalgebra K D) [IsMulCommutative F]
    (hF : Maximal (fun G : Subalgebra K D ↦ IsMulCommutative G) F) :
    letI := fieldOfIsMulCommutative F
    Nonempty (F ⊗[K] D ≃ₐ[F] Matrix (Fin (degree K D)) (Fin (degree K D)) F) := by sorry
