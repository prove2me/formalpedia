-- Prove2me | Theorems.Thm_GroundTheory_Brauer_finrank_eq_degree_sq
-- name    : GroundTheory.Brauer.finrank_eq_degree_sq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:20.940975+00:00
-- url     : https://prove2.me/theorems/c1c97a01-a35d-4075-828d-244341b1a815
-- title:
--   Brauer: finrank eq degree sq
-- statement:
--   The Brauer construction uses the finrank eq degree sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Degree.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Degree.lean#L35-L38

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

theorem GroundTheory.Brauer.finrank_eq_degree_sq [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] :
    finrank K A = degree K A ^ 2 := by sorry
