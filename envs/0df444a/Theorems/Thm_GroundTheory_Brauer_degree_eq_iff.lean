-- Prove2me | Theorems.Thm_GroundTheory_Brauer_degree_eq_iff
-- name    : GroundTheory.Brauer.degree_eq_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:11:53.560841+00:00
-- url     : https://prove2.me/theorems/5fea6ae2-b109-4cba-b80f-8fa4ca9fb8ea
-- title:
--   Brauer: degree eq iff
-- statement:
--   The Brauer construction uses the degree eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Degree.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Degree.lean#L40-L43

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

theorem GroundTheory.Brauer.degree_eq_iff [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] (n : ℕ) :
    degree K A = n ↔ finrank K A = n ^ 2 := by sorry
