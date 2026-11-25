-- Prove2me | Theorems.Thm_GroundTheory_Brauer_exists_finrank_eq_sq
-- name    : GroundTheory.Brauer.exists_finrank_eq_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:11:51.730844+00:00
-- url     : https://prove2.me/theorems/0a4c3911-0845-4b19-8071-9ffbd5b30cc0
-- title:
--   Brauer: exists finrank eq sq
-- statement:
--   The Brauer construction uses the exists finrank eq sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Degree.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Degree.lean#L30-L33

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_Degree
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
open Module TensorProduct
universe u v w
variable (K : Type u) [Field K] (A : Type v) [Ring A] [Algebra K A]

theorem GroundTheory.Brauer.exists_finrank_eq_sq [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] :
    ∃ n : ℕ, finrank K A = n ^ 2 := by sorry
