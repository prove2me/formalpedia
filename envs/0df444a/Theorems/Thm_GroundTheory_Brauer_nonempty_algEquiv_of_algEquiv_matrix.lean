-- Prove2me | Theorems.Thm_GroundTheory_Brauer_nonempty_algEquiv_of_algEquiv_matrix
-- name    : GroundTheory.Brauer.nonempty_algEquiv_of_algEquiv_matrix
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:27.126965+00:00
-- url     : https://prove2.me/theorems/824b8ea3-5397-46ac-bac1-f9f7eaf9f9b2
-- title:
--   Brauer: nonempty alg Equiv of alg Equiv matrix
-- statement:
--   The Brauer construction uses the nonempty alg Equiv of alg Equiv matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/IsBrauerEquivalentIffNonemptyAlgEquiv.lean#L298-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/IsBrauerEquivalentIffNonemptyAlgEquiv.lean#L298-L305

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
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
open TensorProduct
universe u v w
variable {K : Type u} [Field K]

theorem GroundTheory.Brauer.nonempty_algEquiv_of_algEquiv_matrix {D : Type w} [DivisionRing D] [Algebra K D]
    {D' : Type*} [DivisionRing D'] [Algebra K D'] {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Fintype ι'] [DecidableEq ι'] [Nonempty ι']
    (e : Matrix ι ι D ≃ₐ[K] Matrix ι' ι' D') : Nonempty (D ≃ₐ[K] D') := by sorry
