-- Prove2me | Theorems.Thm_GroundTheory_Brauer_degree_tensorProduct
-- name    : GroundTheory.Brauer.degree_tensorProduct
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:11:55.686792+00:00
-- url     : https://prove2.me/theorems/0682aa78-5fa3-451b-883b-17d8e19c8efe
-- title:
--   Brauer: degree tensor Product
-- statement:
--   The Brauer construction uses the degree tensor Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Degree.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Degree.lean#L54-L59

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

theorem GroundTheory.Brauer.degree_tensorProduct [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
    (B : Type w) [Ring B] [Algebra K B] [Algebra.IsCentral K B] [IsSimpleRing B]
    [FiniteDimensional K B] :
    degree K (A ⊗[K] B) = degree K A * degree K B := by sorry
