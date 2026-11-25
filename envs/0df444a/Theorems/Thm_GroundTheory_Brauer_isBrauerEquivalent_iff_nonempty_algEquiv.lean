-- Prove2me | Theorems.Thm_GroundTheory_Brauer_isBrauerEquivalent_iff_nonempty_algEquiv
-- name    : GroundTheory.Brauer.isBrauerEquivalent_iff_nonempty_algEquiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:25.348786+00:00
-- url     : https://prove2.me/theorems/85d59ece-fca8-4c6b-b25e-030df73242fa
-- title:
--   Brauer: is Brauer Equivalent iff nonempty alg Equiv
-- statement:
--   The Brauer construction uses the is Brauer Equivalent iff nonempty alg Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/IsBrauerEquivalentIffNonemptyAlgEquiv.lean#L321-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/IsBrauerEquivalentIffNonemptyAlgEquiv.lean#L321-L334

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

theorem GroundTheory.Brauer.isBrauerEquivalent_iff_nonempty_algEquiv {A B : CSA.{u, v} K} {D : Type w}
    [DivisionRing D] [Algebra K D] {D' : Type*} [DivisionRing D'] [Algebra K D'] {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype ι'] [DecidableEq ι'] [Nonempty ι']
    (eA : A ≃ₐ[K] Matrix ι ι D) (eB : B ≃ₐ[K] Matrix ι' ι' D') :
    IsBrauerEquivalent A B ↔ Nonempty (D ≃ₐ[K] D') := by sorry
