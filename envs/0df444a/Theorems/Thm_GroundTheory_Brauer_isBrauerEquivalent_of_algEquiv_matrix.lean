-- Prove2me | Theorems.Thm_GroundTheory_Brauer_isBrauerEquivalent_of_algEquiv_matrix
-- name    : GroundTheory.Brauer.isBrauerEquivalent_of_algEquiv_matrix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:34.293459+00:00
-- url     : https://prove2.me/theorems/091fcff9-7734-4d08-8d4c-c04500e0db37
-- title:
--   Brauer: is Brauer Equivalent of alg Equiv matrix
-- statement:
--   The Brauer construction uses the is Brauer Equivalent of alg Equiv matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/IsBrauerEquivalentIffNonemptyAlgEquiv.lean#L62-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/IsBrauerEquivalentIffNonemptyAlgEquiv.lean#L62-L71

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

theorem GroundTheory.Brauer.isBrauerEquivalent_of_algEquiv_matrix {A B : CSA.{u, v} K} {C : Type w} [Ring C]
    [Algebra K C] {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype ι']
    [DecidableEq ι'] [Nonempty ι'] (eA : A ≃ₐ[K] Matrix ι ι C) (eB : B ≃ₐ[K] Matrix ι' ι' C) :
    IsBrauerEquivalent A B := by sorry
