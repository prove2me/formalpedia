-- Prove2me | Theorems.Thm_GroundTheory_Brauer_degree_matrix
-- name    : GroundTheory.Brauer.degree_matrix
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:11:48.258527+00:00
-- url     : https://prove2.me/theorems/48f638b9-9291-40c9-afec-e2e6328977a5
-- title:
--   Brauer: degree matrix
-- statement:
--   The Brauer construction uses the degree matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Degree.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Degree.lean#L49-L52

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

theorem GroundTheory.Brauer.degree_matrix [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    degree K (Matrix ι ι A) = Fintype.card ι * degree K A := by sorry
